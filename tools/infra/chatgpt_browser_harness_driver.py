#!/usr/bin/env python3
"""Browser-harness driver for one proposal-only ChatGPT audit turn.

The module is import-safe. The browser-harness globals (`new_tab`, `js`,
`wait_for_load`, etc.) are only required when the functions are executed inside
`browser-harness -c`.
"""

from __future__ import annotations

import json
import hashlib
import os
import subprocess
import time
from pathlib import Path

from tools.infra.chatgpt_lane_guard import browser_chatgpt_lane
from tools.infra.lean_audit_prompt import build_lean_fix_prompt, extract_replacement_lean
from tools.build_lock import acquire_build_lock

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
          const stopBtn = document.querySelector('[data-testid="stop-button"], button#composer-submit-button[data-testid="stop-button"]');
          const buttonText = b => (b.getAttribute('aria-label') || '') + ' ' + (b.innerText || '') + ' ' + (b.getAttribute('data-testid') || '');
          const buttons = Array.from(document.querySelectorAll('button'));
          const streaming = !!stopBtn || buttons.some(b => /Stop answering|Stop generating|stop-button|Stop|Cancel|streaming/i.test(buttonText(b)));
          const fields = Array.from(document.querySelectorAll('#prompt-textarea, textarea[aria-label*="Chat"], textarea, div[contenteditable="true"][role="textbox"], div[contenteditable="true"]'));
          const composerLengths = fields.map(el => {
            const text = el.tagName === 'TEXTAREA' ? el.value : (el.innerText || el.textContent || '');
            return text.trim().length;
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
      const box = document.querySelector('#prompt-textarea, div[contenteditable="true"][role="textbox"], div[contenteditable="true"]');
      const ta = document.querySelector('textarea[aria-label*="Chat"], textarea');
      const fire = (el) => {
        el.dispatchEvent(new InputEvent('input', {bubbles:true, inputType:'insertText', data: prompt}));
        el.dispatchEvent(new Event('change', {bubbles:true}));
      };
      if (box) {
        box.focus();
        document.execCommand('selectAll', false);
        document.execCommand('delete', false);
        const inserted = document.execCommand('insertText', false, prompt);
        if (!inserted || !(box.innerText || box.textContent || '').trim()) {
          box.textContent = prompt;
        }
        fire(box);
      } else if (ta) {
        const setter = Object.getOwnPropertyDescriptor(window.HTMLTextAreaElement.prototype, 'value').set;
        setter.call(ta, prompt);
        ta.focus();
        fire(ta);
      }
      const current = box ? (box.innerText || box.textContent || '') : (ta ? ta.value : '');
      const normalize = s => s.replace(/\\r\\n/g, '\\n').trim();
      return { ok: normalize(current) === normalize(prompt), length: current.length };
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
          const direct = document.querySelector('button#composer-submit-button[data-testid="send-button"], button[data-testid="send-button"]');
          if (direct && !direct.disabled) {
            direct.click();
            return {clicked:true, via:'data-testid-send-button'};
          }
          const candidates = Array.from(document.querySelectorAll('button'));
          const send = candidates.find(b =>
            !b.disabled && (/Send prompt/i.test(b.getAttribute('aria-label') || '') ||
              /Send/i.test((b.getAttribute('aria-label') || '') + ' ' + (b.innerText || '') + ' ' + (b.getAttribute('data-testid') || ''))));
          if (send) {
            send.click();
            return {clicked:true, via:'button'};
          }
          const fields = Array.from(document.querySelectorAll('#prompt-textarea, textarea[aria-label*="Chat"], textarea, div[contenteditable="true"][role="textbox"], div[contenteditable="true"]'));
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
            """(() => {
              if (document.querySelector('[data-testid="stop-button"], button#composer-submit-button[data-testid="stop-button"], [class*="result-streaming"]')) {
                return true;
              }
              return Array.from(document.querySelectorAll('button')).some(
                b => /Stop answering|Stop generating|stop-button|Stop|Cancel|streaming/i.test(
                  (b.getAttribute('aria-label') || '') + ' ' + (b.innerText || '') + ' ' + (b.getAttribute('data-testid') || '')
                )
              );
            })()"""
        )
    )


def assistant_messages() -> list[dict]:
    raw = evaluate(
        """(() => {
          const selectors = [
            '[data-message-author-role="assistant"]',
            'div[class*="assistantMessage"]',
            '[class*="agent-turn"]',
            'article[data-testid*="conversation-turn"] [data-message-author-role="assistant"]'
          ];
          let elements = [];
          for (const sel of selectors) {
            const found = Array.from(document.querySelectorAll(sel));
            if (found.length > 0) {
              elements = found;
              break;
            }
          }
          if (elements.length > 0) {
            const last = elements[elements.length - 1];
            try { last.scrollIntoView({ block: 'end', inline: 'nearest' }); } catch (_) {}
          }
          return JSON.stringify(elements.map((e, i) => ({ index: i, text: (e.innerText || e.textContent || '') })));
        })()"""
    )
    return json.loads(raw or "[]")


def wait_for_final_message(
    timeout_seconds: int = DEFAULT_TIMEOUT_SECONDS,
    poll_seconds: float = DEFAULT_POLL_SECONDS,
    min_message_count: int = 1,
) -> list[dict]:
    print("Waiting for response...")
    deadline = time.time() + timeout_seconds
    last_messages: list[dict] = []
    stable_ticks = 0
    prev_text = ""
    while time.time() < deadline:
        last_messages = assistant_messages()
        is_streaming = streaming()
        if len(last_messages) >= min_message_count:
            last_msg = last_messages[-1].get("text", "").strip()
            if not is_streaming and last_msg and last_msg != "...":
                if last_msg == prev_text:
                    stable_ticks += 1
                else:
                    prev_text = last_msg
                    stable_ticks = 1
                if stable_ticks >= 2:
                    print("Response received.")
                    return last_messages
            else:
                stable_ticks = 0
            print(f"Still waiting... (msg length: {len(last_msg)}, streaming={is_streaming})")
        else:
            print(f"Waiting for assistant turn >= {min_message_count} (current: {len(last_messages)})...")
        time.sleep(poll_seconds)
    if len(last_messages) >= min_message_count and not streaming() and last_messages[-1].get("text", "").strip():
        print("Final response captured at the timeout boundary.")
        return last_messages
    if last_messages:
        raise RuntimeError("response still streaming at timeout; readback required")
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
        before_count = len(assistant_messages())
        set_prompt_exact(prompt_text)
        click_send()
        messages = wait_for_final_message(
            timeout_seconds=timeout,
            poll_seconds=poll_seconds,
            min_message_count=before_count + 1,
        )
        return messages[-1]["text"] if messages else "timeout"


def run_audit_and_save(
    target_file: str | Path,
    context_code: str,
    target_line: int,
    repo_root: str | Path,
    timeout: int = 120,
) -> bool:
    """Full chain: audit -> extract code -> save candidate -> compile once.

    This is intentionally single-shot with respect to ChatGPT. Any retry should
    be scheduled by the queue/worker layer, not by this function.
    It never overwrites ``target_file``.  The browser oracle is an advice tool;
    a coding agent must inspect and apply accepted source edits separately.
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
    candidate_dir = repo_root / "tmp" / "oracle_candidates"
    candidate_dir.mkdir(parents=True, exist_ok=True)
    try:
        relative = target_file.resolve().relative_to(repo_root.resolve())
    except ValueError:
        relative = Path(target_file.name)
    normalized = replacement.rstrip() + "\n"
    digest = hashlib.sha256(normalized.encode("utf-8")).hexdigest()
    candidate_file = candidate_dir / ("__".join(relative.parts) + f".browser.{digest}.lean")
    if candidate_file.exists():
        if candidate_file.read_text(encoding="utf-8") != normalized:
            raise RuntimeError(f"candidate hash collision at {candidate_file}")
    else:
        with candidate_file.open("x", encoding="utf-8") as handle:
            handle.write(normalized)
    print(
        f"Candidate saved: {candidate_file} "
        f"{len(replacement)} chars, {replacement.count(chr(10))} lines"
    )

    with acquire_build_lock(None, f"chatgpt-candidate:{os.getpid()}:{candidate_file.name}", block=True):
        lean = subprocess.run(
            ["lake", "env", "lean", str(candidate_file)],
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
