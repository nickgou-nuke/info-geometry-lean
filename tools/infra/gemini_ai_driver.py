#!/usr/bin/env python3
"""Gemini AI driver for browser-harness.

This is the harness-backed counterpart to the older browser_use-based Gemini
search helper. It reuses the logged-in Chromium session and requires no API
key.

Usage:
    GEMINI_AI_PROMPT_FILE=/tmp/prompt.txt GEMINI_AI_RESULT_JSON=/tmp/result.json \
    browser-harness -c "exec(open('tools/infra/gemini_ai_driver.py').read())"
"""

from pathlib import Path
import json
import os
import time

PROMPT_FILE = Path(os.environ.get("GEMINI_AI_PROMPT_FILE", ""))
RESULT_JSON = Path(os.environ.get("GEMINI_AI_RESULT_JSON", "/tmp/gemini_ai_result.json"))
SENTINEL = "/tmp/gemini_ai_tab_ready"
GEMINI_URL = os.environ.get("GEMINI_AI_URL", "https://gemini.google.com/")


def _eval(expr: str):
    return js(expr)


def _open_gemini() -> None:
    if os.path.exists(SENTINEL):
        current = _eval("return window.location.href;")
        if "gemini.google.com" not in current:
            goto_url(GEMINI_URL)
            wait_for_load()
    else:
        new_tab(GEMINI_URL)
        wait_for_load()
        open(SENTINEL, "w").close()
    time.sleep(2)


def _set_prompt(text: str) -> None:
    safe = json.dumps(text)
    _eval(
        f"""
(() => {{
  const prompt = {safe};
  const el =
    document.querySelector('[role="textbox"]') ||
    document.querySelector('textarea') ||
    document.querySelector('input[type="text"]');
  if (!el) return {{ ok: false, reason: 'missing prompt field' }};
  el.focus();
  if ('value' in el) {{
    const setter = Object.getOwnPropertyDescriptor(window.HTMLTextAreaElement.prototype, 'value')?.set
      || Object.getOwnPropertyDescriptor(window.HTMLInputElement.prototype, 'value')?.set;
    if (setter) setter.call(el, prompt);
    else el.value = prompt;
  }} else {{
    el.textContent = prompt;
    el.innerText = prompt;
  }}
  el.dispatchEvent(new InputEvent('input', {{ bubbles: true, inputType: 'insertText', data: prompt }}));
  el.dispatchEvent(new Event('change', {{ bubbles: true }}));
  return {{ ok: true }};
}})()
"""
    )
    time.sleep(0.5)


def _submit_prompt() -> None:
    result = _eval(
        """
(() => {
  const el = document.querySelector('[role="textbox"]') || document.querySelector('textarea') || document.querySelector('input[type="text"]');
  if (!el) return { submitted: false, reason: 'missing prompt field' };
  el.focus();
  el.dispatchEvent(new KeyboardEvent('keydown', {
    key: 'Enter',
    code: 'Enter',
    keyCode: 13,
    which: 13,
    bubbles: true,
    cancelable: true
  }));
  el.dispatchEvent(new KeyboardEvent('keypress', {
    key: 'Enter',
    code: 'Enter',
    keyCode: 13,
    which: 13,
    bubbles: true,
    cancelable: true
  }));
  el.dispatchEvent(new KeyboardEvent('keyup', {
    key: 'Enter',
    code: 'Enter',
    keyCode: 13,
    which: 13,
    bubbles: true,
    cancelable: true
  }));
  return { submitted: true, via: 'enter' };
})()
"""
    )
    if not result or not result.get("submitted"):
        raise RuntimeError("failed to submit Gemini prompt")
    time.sleep(1)


def _wait_for_response(timeout: int = 120) -> str:
    stable = 0
    last = ""
    for _ in range(max(1, timeout // 3)):
        time.sleep(3)
        body = _eval("return (document.body.innerText || '')")
        tail = body[-800:]
        if tail == last:
            stable += 1
            if stable >= 3:
                return body
        else:
            stable = 0
            last = tail
    return _eval("return (document.body.innerText || '')")


def _extract_links() -> list[dict]:
    raw = _eval(
        """JSON.stringify(
  Array.from(document.querySelectorAll('a[href^="http"]'))
    .filter(a => {
      const t = (a.innerText || '').trim();
      return t.length > 10 && !a.href.includes('gemini.google.com');
    })
    .slice(0, 10)
    .map(a => ({ title: (a.innerText || '').trim().slice(0, 150), url: a.href }))
)"""
    )
    try:
        return json.loads(raw or "[]")
    except Exception:
        return []


def main() -> None:
    if not PROMPT_FILE.exists():
        raise RuntimeError("GEMINI_AI_PROMPT_FILE must point to an existing prompt file")

    prompt = PROMPT_FILE.read_text(encoding="utf-8")
    _open_gemini()
    _set_prompt(prompt)
    _submit_prompt()
    body = _wait_for_response(timeout=int(os.environ.get("GEMINI_AI_TIMEOUT_SECONDS", "120")))

    idx = body.find("Gemini")
    summary = body[idx:idx + 6000] if idx >= 0 else body[:6000]
    result = {"summary": summary, "links": _extract_links()}
    RESULT_JSON.write_text(json.dumps(result), encoding="utf-8")
    print(f"Gemini AI: {len(result['summary'])} chars, {len(result['links'])} links")


if __name__ == "__main__":
    main()
