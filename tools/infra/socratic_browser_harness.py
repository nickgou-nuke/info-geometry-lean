#!/usr/bin/env python3
"""
Socratic Verifier Browser-Harness Driver

Implements the Socratic Verifier role using browser-harness + ChatGPT
instead of aiClaw. Mirrors the Oracle Referee pattern.

Usage:
    python3 socratic_browser_harness.py --file file.lean --theorem name --mode critique
    python3 socratic_browser_harness.py --file file.lean --theorem name --mode repair --errors "errors text"
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

DEFAULT_CHATGPT_URL = os.environ.get("CHATGPT_URL", "https://chatgpt.com/?temporary-chat=true")
DEFAULT_TIMEOUT = int(os.environ.get("CHATGPT_TIMEOUT_SECONDS", "600"))
DEFAULT_POLL = float(os.environ.get("CHATGPT_POLL_SECONDS", "5"))
DEFAULT_RESULT_JSON = Path(os.environ.get("CHATGPT_RESULT_JSON", "/tmp/socratic_browser_result.json"))

CHATGPT_SENTINEL = "/tmp/socratic_chatgpt_tab_ready"


def _prompt_field_ready() -> bool:
    result = js(
        """(() => {
          const el = document.querySelector('textarea[aria-label*="Chat"], textarea, div[contenteditable="true"][role="textbox"], div[contenteditable="true"]');
          return { ok: !!el };
        })()"""
    )
    return bool(result.get("ok"))


def _wait_for_prompt_field(timeout_seconds: int = 30, poll_seconds: float = 1.0) -> None:
    deadline = time.time() + timeout_seconds
    while time.time() < deadline:
        if _prompt_field_ready():
            return
        time.sleep(poll_seconds)
    raise RuntimeError("BROWSER_UNAVAILABLE: ChatGPT prompt field not ready")


def _reset_sentinel() -> None:
    try:
        os.unlink("/tmp/socratic_chatgpt_tab_ready")
    except FileNotFoundError:
        pass


def _sentinel_exists() -> bool:
    return os.path.exists("/tmp/socratic_chatgpt_tab_ready")


def open_chatgpt(chatgpt_url: str = DEFAULT_CHATGPT_URL) -> None:
    if _sentinel_exists():
        print(f"Reusing existing Socratic ChatGPT tab")
        current = js("return window.location.href;")
        if "chatgpt.com" not in current:
            goto_url(chatgpt_url)
            wait_for_load()
    else:
        print(f"Opening {chatgpt_url}...")
        new_tab(chatgpt_url)
        wait_for_load()
        open("/tmp/socratic_chatgpt_tab_ready", "w").close()
    time.sleep(2)
    if not _prompt_field_ready():
        print("Stale Socratic sentinel detected; reopening tab.")
        _reset_sentinel()
        new_tab(chatgpt_url)
        wait_for_load()
        open("/tmp/socratic_chatgpt_tab_ready", "w").close()
        time.sleep(2)
    _wait_for_prompt_field()
    print("Socratic ChatGPT tab ready.")


def set_prompt_exact(text: str) -> dict:
    print("Inserting prompt...")
    expr = f"""(() => {{
      const prompt = {json.dumps(text)};
      const ta = document.querySelector('textarea[aria-label*="Chat"], textarea');
      const box = document.querySelector('div[contenteditable="true"][role="textbox"], div[contenteditable="true"]');
      const fire = (el) => {{
        el.dispatchEvent(new InputEvent('input', {{bubbles:true, inputType:'insertText', data: prompt}}));
        el.dispatchEvent(new Event('change', {{bubbles:true}}));
      }};
      if (box) {{ box.focus(); box.textContent = prompt; fire(box); }}
      if (ta) {{
        const setter = Object.getOwnPropertyDescriptor(window.HTMLTextAreaElement.prototype, 'value').set;
        setter.call(ta, prompt);
        ta.focus();
        fire(ta);
      }}
      const current = box ? box.innerText : (ta ? ta.value : '');
      return {{ ok: current === prompt }};
    }})()"""
    result = js(expr)
    if not result.get("ok"):
        raise RuntimeError(f"prompt insertion mismatch: {result}")
    print("Prompt inserted.")
    return result


def click_send() -> None:
    print("Clicking send...")
    deadline = time.time() + 10
    last_result: dict | None = None
    while time.time() < deadline:
        assert_not_streaming()
        result = js("""(() => {
          const candidates = Array.from(document.querySelectorAll('button'));
          const send = candidates.find(b =>
            !b.disabled && (/Send prompt/i.test(b.getAttribute('aria-label') || '') ||
              /Send/i.test((b.getAttribute('aria-label') || '') + ' ' + (b.innerText || '') + ' ' + (b.getAttribute('data-testid') || ''))));
          if (send) {
            send.click();
            return {clicked:true, via:'button'};
          }
          const fields = Array.from(document.querySelectorAll('textarea[aria-label*="Chat"], textarea, div[contenteditable="true"][role="textbox"], div[contenteditable="true"]'));
          const composerLengths = fields.map(el => {
            const text = el.tagName === 'TEXTAREA' ? el.value : (el.innerText || el.textContent || '');
            return text.length;
          });
          return {clicked:false, reason:'send_button_missing', composerLengths};
        })()""")
        last_result = result
        if result.get("clicked"):
            print(f"Send submitted via {result.get('via', 'unknown')}.")
            return
        time.sleep(0.5)
    raise RuntimeError(f"failed to submit prompt: {last_result}")


def streaming() -> bool:
    return bool(
        js(
            """Array.from(document.querySelectorAll('button')).some(b => /Stop|Cancel|streaming/i.test((b.getAttribute('aria-label') || '') + ' ' + (b.innerText || '')))"""
        )
    )


def assistant_messages() -> list[dict]:
    raw = js(
        """JSON.stringify(Array.from(document.querySelectorAll('[data-message-author-role="assistant"]')).map((e, i) => ({ index: i, text: e.innerText || '' })))"""
    )
    return json.loads(raw or "[]")


def wait_for_final_message(
    timeout_seconds: int = DEFAULT_TIMEOUT,
    poll_seconds: float = DEFAULT_POLL,
) -> list[dict]:
    print("Waiting for response...")
    deadline = time.time() + timeout_seconds
    last_messages: list[dict] = []
    while time.time() < deadline:
        last_messages = assistant_messages()
        is_streaming = streaming()
        if last_messages:
            last_msg = last_messages[-1].get("text", "").strip()
            if not is_streaming and last_msg:
                print("Response received.")
                return last_messages
            print(f"Still waiting... (msg length: {len(last_msg)})")
        else:
            print("No messages yet...")
        time.sleep(poll_seconds)
    if last_messages:
        print("Timed out waiting for final stop signal; returning latest collected message.")
        return last_messages
    raise RuntimeError("timed out waiting for final message")


def run_socratic_critique(hypothesis: str, rationale: str, objects: list[str], apex: str) -> str:
    """Run Socratic critique via browser-harness."""
    prompt = f"""Socratic critique of mathematical hypothesis:

HYPOTHESIS: {hypothesis}
RATIONALE: {rationale}
OBJECTS: {', '.join(map(str, objects)) if isinstance(rationale, list) else rationale}
SOURCE APEX: {apex}

Provide a structured critique:
1. Mathematical soundness (true/false/uncertain)
2. Missing assumptions
3. Potential counterexamples
4. Suggested formalization approach in Lean 4
5. Related existing theorems in infogeometry DAG (if known)
"""

    with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False) as f:
        f.write(prompt)
        prompt_file = f.name

    env = os.environ.copy()
    env["CHATGPT_PROMPT_FILE"] = "/tmp/socratic_prompt.txt"
    env["BU_CDP_WS"] = os.environ.get("BU_CDP_WS", "")
    env["CHATGPT_URL"] = "https://chatgpt.com/?temporary-chat=true"
    env["CHATGPT_RESULT_JSON"] = "/tmp/socratic_browser_result.json"
    env["CHATGPT_TIMEOUT_SECONDS"] = "600"
    env["CHATGPT_POLL_SECONDS"] = "5"

    Path("/tmp/socratic_prompt.txt").write_text(
        f"""Socratic critique of mathematical hypothesis:

HYPOTHESIS: {hypothesis}
RATIONALE: {rationale}
OBJECTS: {rationale if isinstance(rationale, list) else ''}
SOURCE APEX: {rationale if isinstance(rationale, str) else ''}

Provide a structured critique:
1. Mathematical soundness (true/false/uncertain)
2. Missing assumptions
3. Potential counterexamples
4. Suggested formalization approach in Lean 4
5. Related existing theorems in infogeometry DAG (if known)""")

    script_payload = f"""import sys
sys.path.insert(0, "{REPO_ROOT}")
exec(open("{REPO_ROOT}/tools/infra/chatgpt_browser_harness_driver.py").read())
_main()
"""

    print("Running Socratic critique via browser-harness...")
    result = subprocess.run(
        ["browser-harness"],
        input=script_payload,
        cwd=REPO_ROOT,
        env={**os.environ, "CHATGPT_PROMPT_FILE": "/tmp/socratic_prompt.txt", "BU_CDP_WS": os.environ.get("BU_CDP_WS", ""), "CHATGPT_URL": "https://chatgpt.com/?temporary-chat=true", "CHATGPT_RESULT_JSON": "/tmp/socratic_browser_result.json", "CHATGPT_TIMEOUT_SECONDS": "600", "CHATGPT_POLL_SECONDS": "5"},
        capture_output=True,
        text=True,
        timeout=600,
    )

    result_file = Path("/tmp/socratic_browser_result.json")
    if result_file.exists():
        return result_file.read_text()
    return (result.stdout + "\n" + result.stderr).strip() or "No response"


def run_socratic_repair(hypothesis: str, lean_errors: str) -> str:
    """Run Socratic repair via browser-harness."""
    prompt = f"""Lean 4 compilation errors for hypothesis:
{hypothesis}

ERRORS:
{lean_errors}

Provide a concrete repair patch:
- Identify the exact Lean syntax/type error
- Suggest the corrected Lean code
- Explain the mathematical correction
"""

    with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False) as f:
        f.write(prompt)
        prompt_file = f.name

    env = os.environ.copy()
    env["CHATGPT_PROMPT_FILE"] = "/tmp/socratic_prompt.txt"
    env["BU_CDP_WS"] = os.environ.get("BU_CDP_WS", "")
    env["CHATGPT_URL"] = "https://chatgpt.com/?temporary-chat=true"
    env["CHATGPT_RESULT_JSON"] = "/tmp/socratic_browser_result.json"
    env["CHATGPT_TIMEOUT_SECONDS"] = "600"
    env["CHATGPT_POLL_SECONDS"] = "5"

    Path("/tmp/socratic_prompt.txt").write_text(f"""Lean 4 compilation errors for hypothesis:
{hypothesis}

ERRORS:
{lean_errors}

Provide a concrete repair patch:
- Identify the exact Lean syntax/type error
- Suggest the corrected Lean code
- Explain the mathematical correction""")

    cmd = [
        "browser-harness", "-c",
        f'import sys; sys.path.insert(0, "{REPO_ROOT}"); '
        f'exec(open("tools/infra/chatgpt_browser_harness_driver.py").read()); _main()'
    ]

    print("Running Socratic repair via browser-harness...")
    result = subprocess.run(
        cmd,
        cwd=REPO_ROOT,
        env={**os.environ, "CHATGPT_PROMPT_FILE": "/tmp/socratic_prompt.txt", "BU_CDP_WS": os.environ.get("BU_CDP_WS", ""), "CHATGPT_URL": "https://chatgpt.com/?temporary-chat=true", "CHATGPT_RESULT_JSON": "/tmp/socratic_browser_result.json", "CHATGPT_TIMEOUT_SECONDS": "600", "CHATGPT_POLL_SECONDS": "5"},
        capture_output=True,
        text=True,
        timeout=600,
    )

    result_file = Path("/tmp/socratic_browser_result.json")
    if result_file.exists():
        return result_file.read_text()
    return result.stdout or "No response"


def main():
    parser = argparse.ArgumentParser(description="Socratic Verifier via Browser Harness")
    parser.add_argument("--mode", choices=["critique", "repair"], required=True)
    parser.add_argument("--hypothesis", help="Hypothesis statement")
    parser.add_argument("--rationale", help="Rationale")
    parser.add_argument("--objects", help="Comma-separated mathematical objects")
    parser.add_argument("--apex", help="Source apex")
    parser.add_argument("--errors", help="Lean errors for repair mode")
    parser.add_argument("--output", help="Output file")
    args = parser.parse_args()

    if args.mode == "critique":
        if not args.hypothesis or not args.rationale:
            print("Error: --hypothesis and --rationale required for critique mode")
            sys.exit(1)
        objects = args.objects.split(",") if args.objects else []
        result = run_socratic_critique(args.hypothesis, args.rationale, objects, args.apex or "")
        print(result)
        if args.output:
            Path(args.output).write_text(result)
    elif args.mode == "repair":
        if not args.errors:
            print("Error: --errors required for repair mode")
            sys.exit(1)
        result = run_socratic_repair(args.hypothesis, args.errors)
        print(result)
        if args.output:
            Path(args.output).write_text(result)


if __name__ == "__main__":
    main()