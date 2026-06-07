#!/usr/bin/env python3
"""Google AI Mode literature search via browser-harness.

Connects to the existing Chromium DevTools endpoint, searches Google AI Mode
through `tools/infra/google_ai_driver.py`, and returns enriched context.

Usage:
    python3 tools/infra/google_ai_searcher.py "Hodge star operator Lean 4 proof"
"""
from __future__ import annotations
import asyncio
import json
import os
import subprocess
import sys
import time
import tempfile
import urllib.request
from pathlib import Path

_REPO = Path(__file__).resolve().parents[2]
GOOGLE_SCRIPT = _REPO / "tools" / "infra" / "google_ai_driver.py"

try:
    from tools.infra.agent_message_ledger import record_message
except Exception:  # pragma: no cover - observation must never block search.
    record_message = None


async def search_google_ai(query: str, cdp_url: str = "http://127.0.0.1:9222") -> dict:
    """Search Google AI Mode and return structured results with references."""
    task = (
        f"Search Google for: {query}. "
        "Summarize the AI Mode answer and top results. Include enough source names "
        "for proof-context triage, but do not invent citations."
    )
    started = time.monotonic()
    timeout = int(os.environ.get("GOOGLE_AI_TIMEOUT_SECONDS", "150"))

    def run_browser_harness() -> tuple[int, str, str, dict]:
        with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False) as prompt_file:
            prompt_file.write(task)
            prompt_path = prompt_file.name
        with tempfile.NamedTemporaryFile(mode="w", suffix=".json", delete=False) as result_file:
            result_path = result_file.name

        env = os.environ.copy()
        env["GOOGLE_AI_PROMPT_FILE"] = prompt_path
        env["GOOGLE_AI_RESULT_JSON"] = result_path
        env["GOOGLE_AI_TIMEOUT_SECONDS"] = str(timeout)
        if "BU_CDP_WS" not in env:
            detected = detect_cdp_ws(cdp_url)
            if detected:
                env["BU_CDP_WS"] = detected

        try:
            proc = subprocess.run(
                ["browser-harness", "-c", f"exec(open('{GOOGLE_SCRIPT}').read())"],
                cwd=str(_REPO),
                env=env,
                capture_output=True,
                text=True,
                timeout=timeout + 60,
            )
            parsed = {}
            result_file_path = Path(result_path)
            if result_file_path.exists() and result_file_path.stat().st_size > 0:
                try:
                    parsed = json.loads(result_file_path.read_text(encoding="utf-8"))
                except json.JSONDecodeError:
                    parsed = {"summary": result_file_path.read_text(encoding="utf-8")[:2000], "links": []}
            return proc.returncode, proc.stdout, proc.stderr, parsed
        finally:
            for path in (prompt_path, result_path):
                try:
                    Path(path).unlink()
                except FileNotFoundError:
                    pass

    returncode, stdout, stderr, parsed = await asyncio.to_thread(run_browser_harness)
    summary = str(parsed.get("summary") or "")
    links = parsed.get("links") if isinstance(parsed.get("links"), list) else []
    result = {"summary": summary, "references": links, "links": links}
    success = returncode == 0 and bool(summary.strip())

    if record_message is not None:
        try:
            record_message(
                source_tool="google_ai_searcher.py",
                source_file="tools/infra/google_ai_searcher.py",
                channel="google_ai_browser_harness_search",
                direction="agent_to_model",
                provider="browser-harness",
                model="google_ai",
                platform="google_ai",
                prompt_text=task,
                response_text=summary or stdout or stderr,
                success=success,
                latency_ms=(time.monotonic() - started) * 1000.0,
                metadata={
                    "query": query,
                    "returncode": returncode,
                    "failure_pattern": "" if success else (stderr or stdout)[:160],
                },
            )
        except Exception:
            pass

    if success:
        return result

    fallback = summary or stdout or stderr
    return {"summary": fallback[:2000], "references": [], "links": []}


def detect_cdp_ws(cdp_url: str) -> str:
    if cdp_url.startswith("ws://") or cdp_url.startswith("wss://"):
        return cdp_url
    url = cdp_url.rstrip("/") + "/json/version"
    try:
        with urllib.request.urlopen(url, timeout=2) as response:
            payload = json.loads(response.read().decode("utf-8"))
        return str(payload.get("webSocketDebuggerUrl") or "")
    except Exception:
        return ""


def enrich_context(query: str, context_code: str, cdp_url: str = "http://127.0.0.1:9222") -> str:
    """Enrich Lean proof context with Google AI Mode literature search.

    Blocking wrapper — runs the async search synchronously.
    """
    result = asyncio.run(search_google_ai(query, cdp_url=cdp_url))
    summary = result.get("summary", "")
    refs = result.get("references", [])

    if not summary and not refs:
        return context_code

    parts = [context_code]
    parts.append("\n/* ===== Google AI Mode Literature Context =====")
    parts.append(summary[:2000])
    if refs:
        parts.append("--- References ---")
        for i, r in enumerate(refs[:5], 1):
            title = r.get("title", "")[:150]
            url = r.get("url", "")
            snippet = r.get("snippet", "")[:200]
            parts.append(f"[{i}] {title} — {url}")
            if snippet:
                parts.append(f"    {snippet}")
    parts.append("===== End Literature Context ===== */\n")
    return "\n".join(parts)


if __name__ == "__main__":
    query = sys.argv[1] if len(sys.argv) > 1 else "Hodge star operator Lean 4 proof"
    result = asyncio.run(search_google_ai(query))
    print(json.dumps(result, indent=2))
