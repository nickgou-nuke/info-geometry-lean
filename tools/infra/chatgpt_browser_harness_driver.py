#!/usr/bin/env python3
"""Browser-harness driver for one proposal-only ChatGPT audit turn.

The module is import-safe. The browser-harness globals (`new_tab`, `js`,
`wait_for_load`, etc.) are only required when the functions are executed inside
`browser-harness -c`.
"""

from __future__ import annotations

import json
import os
import subprocess
import time
from pathlib import Path

from tools.infra.chatgpt_lane_guard import browser_chatgpt_lane
from tools.infra.lean_audit_prompt import build_lean_fix_prompt, extract_replacement_lean

DEFAULT_CHATGPT_URL = os.environ.get(
    "CHATGPT_URL", "https://chatgpt.com/?temporary-chat=true"
)
DEFAULT_TIMEOUT_SECONDS = int(os.environ.get("CHATGPT_TIMEOUT_SECONDS", "600"))
DEFAULT_POLL_SECONDS = float(os.environ.get("CHATGPT_POLL_SECONDS", "5"))
DEFAULT_RESULT_JSON = Path(
    os.environ.get("CHATGPT_RESULT_JSON", "/tmp/chatgpt_browser_result.json")
)


def evaluate(expr: str):
    return js(expr)


CHATGPT_SENTINEL = "/tmp/chatgpt_audit_tab_ready"


def _prompt_field_ready() -> bool:
    result = evaluate(
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


def _reset_chatgpt_sentinel() -> None:
    try:
        os.unlink(CHATGPT_SENTINEL)
    except FileNotFoundError:
        pass


def browser_send_state() -> dict:
    return evaluate(
        """(() => {
          const buttonText = b => (b.getAttribute('aria-label') || '') + ' ' + (b.innerText || '');
          const buttons = Array.from(document.querySelectorAll('button'));
          const streaming = buttons.some(b => /Stop answering|Stop generating|Stop|Cancel|streaming/i.test(buttonText(b)));
          const fields = Array.from(document.querySelectorAll('textarea[aria-label*="Chat"], textarea, div[contenteditable="true"][role="textbox"], div[contenteditable="true"]'));
          const composerLengths = fields.map(el => {
            const text = el.tagName === 'TEXTAREA' ? el.value : (el.innerText || el.textContent || '');
            return text.length;
          });
          return { streaming, composerLengths };
        })()"""
    )


def assert_not_streaming() -> None:
    state = browser_send_state()
    if state.get("streaming"):
        raise RuntimeError(
            "CHATGPT_LANE_BUSY: visible Stop/Cancel/streaming control is present; "
            "recover the final visible answer before sending another prompt"
        )


def assert_composer_empty() -> None:
    state = browser_send_state()
    lengths = state.get("composerLengths") or []
    if any(int(length) > 0 for length in lengths):
        raise RuntimeError(
            "CHATGPT_COMPOSER_NOT_EMPTY: refusing to overwrite an unsent prompt; "
            f"composer_lengths={lengths}"
        )


def open_chatgpt(chatgpt_url: str = DEFAULT_CHATGPT_URL) -> None:
    if os.path.exists(CHATGPT_SENTINEL):
        print(f"Reusing existing ChatGPT tab")
        current = js("return window.location.href;")
        if "chatgpt.com" not in current:
            goto_url(chatgpt_url)
            wait_for_load()
    else:
        print(f"Opening {chatgpt_url}...")
        new_tab(chatgpt_url)
        wait_for_load()
        open(CHATGPT_SENTINEL, "w").close()
    time.sleep(2)
    if not _prompt_field_ready():
        print("Stale ChatGPT sentinel detected; reopening tab.")
        _reset_chatgpt_sentinel()
        new_tab(chatgpt_url)
        wait_for_load()
        open(CHATGPT_SENTINEL, "w").close()
        time.sleep(2)
    _wait_for_prompt_field()
    print("Tab ready.")


def set_prompt_exact(text: str) -> dict:
    print("Inserting prompt...")
    assert_not_streaming()
    assert_composer_empty()
    expr = """(() => {
      const prompt = %s;
      const ta = document.querySelector('textarea[aria-label*="Chat"], textarea');
      const box = document.querySelector('div[contenteditable="true"][role="textbox"], div[contenteditable="true"]');
      const fire = (el) => {
        el.dispatchEvent(new InputEvent('input', {bubbles:true, inputType:'insertText', data: prompt}));
        el.dispatchEvent(new Event('change', {bubbles:true}));
      };
      if (box) { box.focus(); box.textContent = prompt; fire(box); }
      if (ta) {
        const setter = Object.getOwnPropertyDescriptor(window.HTMLTextAreaElement.prototype, 'value').set;
        setter.call(ta, prompt);
        ta.focus();
        fire(ta);
      }
      const current = box ? box.innerText : (ta ? ta.value : '');
      return { ok: current === prompt };
    })()""" % json.dumps(text)
    result = evaluate(expr)
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
        result = evaluate("""(() => {
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
        evaluate(
            """Array.from(document.querySelectorAll('button')).some(b => /Stop|Cancel|streaming/i.test((b.getAttribute('aria-label') || '') + ' ' + (b.innerText || '')))"""
        )
    )


def assistant_messages() -> list[dict]:
    raw = evaluate(
        """JSON.stringify(Array.from(document.querySelectorAll('[data-message-author-role="assistant"]')).map((e, i) => ({ index: i, text: e.innerText || '' })))"""
    )
    return json.loads(raw or "[]")


def wait_for_final_message(
    timeout_seconds: int = DEFAULT_TIMEOUT_SECONDS,
    poll_seconds: float = DEFAULT_POLL_SECONDS,
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
    raise RuntimeError("timed out")


def run_audit(
    prompt_text: str,
    timeout: int = DEFAULT_TIMEOUT_SECONDS,
    *,
    chatgpt_url: str = DEFAULT_CHATGPT_URL,
    poll_seconds: float = DEFAULT_POLL_SECONDS,
) -> str:
    """Send *prompt_text* to ChatGPT and return the last assistant message."""
    with browser_chatgpt_lane(
        source="chatgpt_browser_harness_driver",
        platform="chatgpt",
        prompt_chars=len(prompt_text),
    ):
        open_chatgpt(chatgpt_url)
        if not _prompt_field_ready():
            raise RuntimeError("BROWSER_UNAVAILABLE: prompt field missing after tab open")
        assert_not_streaming()
        set_prompt_exact(prompt_text)
        click_send()
        messages = wait_for_final_message(timeout_seconds=timeout, poll_seconds=poll_seconds)
        return messages[-1]["text"] if messages else "timeout"


def run_audit_and_save(
    target_file: str | Path,
    context_code: str,
    target_line: int,
    repo_root: str | Path,
    timeout: int = 120,
) -> bool:
    """Full chain: audit -> extract code -> save -> compile once.

    This is intentionally single-shot with respect to ChatGPT. Any retry should
    be scheduled by the queue/worker layer, not by this function.
    """
    result = run_audit(context_code, timeout=timeout)
    if not result or result == "timeout":
        print("AUDIT_FAILED: no response")
        return False

    replacement = extract_replacement_lean(result)
    if not replacement:
        print("AUDIT_FAILED: no replacement Lean file")
        return False

    target_file = Path(target_file)
    repo_root = Path(repo_root)
    target_file.write_text(replacement, encoding="utf-8")
    print(f"Saved: {len(replacement)} chars, {replacement.count(chr(10))} lines")

    lean = subprocess.run(
        ["lake", "env", "lean", str(target_file)],
        capture_output=True,
        text=True,
        timeout=60,
        cwd=str(repo_root),
    )

    if lean.returncode == 0:
        print("COMPILE_SUCCESS")
        return True

    error_output = (lean.stderr or "")[:2000]
    print(f"COMPILE_FAILED: {error_output[:200]}...")
    return False


def send_fix(error_text: str) -> str:
    """Continue the conversation with a compilation error fix request."""
    return run_audit(
        build_lean_fix_prompt(
            target_name="compilation-error-fix",
            context_code="",
            error_text=error_text[:1000],
        ),
        timeout=60,
    )


def _main() -> None:
    prompt_file = Path(os.environ.get("CHATGPT_PROMPT_FILE", ""))
    if not prompt_file.exists():
        raise RuntimeError("CHATGPT_PROMPT_FILE must point to an existing prompt file")
    prompt = prompt_file.read_text(encoding="utf-8")
    result = run_audit(prompt)
    DEFAULT_RESULT_JSON.write_text(result, encoding="utf-8")
    print(f"DONE: Result saved to {DEFAULT_RESULT_JSON}")


if __name__ == "__main__":
    _main()
