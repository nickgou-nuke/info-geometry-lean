#!/usr/bin/env python3
"""
LeanCopilot ExternalModel adapter for the aiClaw localBridge.

Translates between LeanCopilot's /generate REST API and the repo-owned aiClaw
queue adapter. This must not call localBridge directly; direct calls bypass the
single-flight ChatGPT lane and can stack prompts while the browser is still
thinking.

Usage:
    python3 lean_copilot_adapter.py [--port 23337] [--bridge-url http://127.0.0.1:10088]

Then configure LeanCopilot to use:
    ExternalGenerator { name := "lean-adapter", host := "localhost", port := 23337 }
"""

import json
import argparse
import http.server
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.infra.aiclaw_chat import ask_ai  # noqa: E402


TACTIC_FENCE_RE = re.compile(r"```(?:lean4?|text)?\s*(.*?)```", re.DOTALL | re.IGNORECASE)


def build_oracle_prompt(state: str, prefix: str) -> str:
    prefix_line = f"\nRequired tactic prefix: {prefix}\n" if prefix else ""
    return f"""You are a Lean 4 tactic suggester for LeanCopilot.
Return ONLY compact JSON with this exact shape:
{{"outputs":[{{"output":"<one Lean tactic>","score":0.0}}]}}

Rules:
- Output JSON only. No Markdown, prose, explanation, or code fences.
- Each output must be a single Lean tactic fragment, not a whole theorem.
- Prefer short tactics: rfl, exact ..., simpa ..., simp [...], rw [...], ring, omega, aesop.
- Do not use sorry, admit, axiom, unsafe, by_contra! unless already justified by context.
- Do not reference declarations not visible in the tactic state.
{prefix_line}
Lean tactic state:
```lean
{state}
```"""


def parse_outputs(content: str) -> list[dict[str, float | str]]:
    text = content.strip()
    candidates = [text]
    candidates.extend(match.group(1).strip() for match in TACTIC_FENCE_RE.finditer(text))
    for candidate in candidates:
        try:
            data = json.loads(candidate)
        except json.JSONDecodeError:
            continue
        outputs = data.get("outputs") if isinstance(data, dict) else None
        if not isinstance(outputs, list):
            continue
        parsed = []
        for item in outputs:
            if not isinstance(item, dict):
                continue
            output = str(item.get("output") or "").strip()
            if not output:
                continue
            if "sorry" in output or "admit" in output or "axiom" in output:
                continue
            try:
                score = float(item.get("score", 0.0))
            except (TypeError, ValueError):
                score = 0.0
            parsed.append({"output": output, "score": score})
        if parsed:
            return parsed
    return []


class LeanCopilotAdapterHandler(http.server.BaseHTTPRequestHandler):
    bridge_url = "http://127.0.0.1:10088"
    platform = "chatgpt"
    timeout = 240
    queue_timeout = 900

    def do_POST(self):
        if self.path != "/generate":
            self.send_response(404)
            self.end_headers()
            self.wfile.write(b'{"error":"not_found"}')
            return

        length = int(self.headers.get("Content-Length", 0))
        body = self.rfile.read(length) if length > 0 else b"{}"
        try:
            req = json.loads(body)
        except json.JSONDecodeError:
            self._json(400, {"error": "invalid_json"})
            return

        state = str(req.get("input", ""))
        prefix = str(req.get("prefix", ""))
        prompt = build_oracle_prompt(state, prefix)

        try:
            result = ask_ai(
                base_url=self.bridge_url,
                platform=self.platform,
                prompt=prompt,
                timeout=self.timeout,
                wait=False,
                navigate=False,
                new=False,
                allow_sensitive=False,
                queue=True,
                queue_timeout=self.queue_timeout,
                hold_on_suspect=True,
            )
        except Exception as e:
            self._json(504, {
                "error": f"aiClaw bridge error: {e}",
                "outputs": []
            })
            return

        if result.get("suspect_intermediate"):
            self._json(409, {
                "error": "aiClaw returned an intermediate Thinking payload; lane held for recovery",
                "outputs": []
            })
            return

        content = str(result.get("content") or "")
        outputs = parse_outputs(content)
        if not outputs:
            self._json(422, {
                "error": "no valid tactic JSON outputs found in aiClaw response",
                "outputs": []
            })
            return

        self._json(200, {"outputs": outputs})

    def _json(self, status, data):
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.end_headers()
        self.wfile.write(json.dumps(data).encode("utf-8"))

    def log_message(self, format, *args):
        pass  # suppress HTTP log noise


def main():
    parser = argparse.ArgumentParser(description="LeanCopilot aiClaw adapter")
    parser.add_argument("--port", type=int, default=23337,
                        help="Port for LeanCopilot to connect to (default: 23337)")
    parser.add_argument("--bridge-url", default="http://127.0.0.1:10088",
                        help="aiClaw localBridge URL (default: http://127.0.0.1:10088)")
    parser.add_argument("--platform", default="chatgpt",
                        help="aiClaw platform name (default: chatgpt)")
    parser.add_argument("--timeout", type=int, default=240,
                        help="aiClaw request timeout in seconds (default: 240)")
    parser.add_argument("--queue-timeout", type=float, default=900,
                        help="aiClaw lane queue timeout in seconds (default: 900)")
    args = parser.parse_args()

    LeanCopilotAdapterHandler.bridge_url = args.bridge_url
    LeanCopilotAdapterHandler.platform = args.platform
    LeanCopilotAdapterHandler.timeout = args.timeout
    LeanCopilotAdapterHandler.queue_timeout = args.queue_timeout

    server = http.server.HTTPServer(("127.0.0.1", args.port), LeanCopilotAdapterHandler)
    print(f"LeanCopilot adapter listening on 127.0.0.1:{args.port}")
    print(f"Forwarding to aiClaw bridge at {args.bridge_url}")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nShutting down.")


if __name__ == "__main__":
    main()
