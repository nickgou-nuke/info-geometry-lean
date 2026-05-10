# Browser-harness script for one proposal-only ChatGPT audit turn.
from __future__ import annotations
import json, os, time
from pathlib import Path

PROMPT_FILE = Path(os.environ.get("CHATGPT_PROMPT_FILE", ""))
RESULT_JSON = Path(os.environ.get("CHATGPT_RESULT_JSON", "/tmp/chatgpt_browser_result.json"))
CHATGPT_URL = os.environ.get("CHATGPT_URL", "https://chatgpt.com/?temporary-chat=true")
TIMEOUT_SECONDS = int(os.environ.get("CHATGPT_TIMEOUT_SECONDS", "600"))
POLL_SECONDS = float(os.environ.get("CHATGPT_POLL_SECONDS", "5"))

if not PROMPT_FILE.exists(): raise RuntimeError("CHATGPT_PROMPT_FILE must point to an existing prompt file")
prompt = PROMPT_FILE.read_text(encoding="utf-8")

def evaluate(expr: str): return js(expr)
def open_chatgpt() -> None:
    print(f"Opening {CHATGPT_URL}...")
    new_tab(CHATGPT_URL)
    wait_for_load()
    time.sleep(2)
    print("Page loaded.")

def set_prompt_exact(text: str) -> dict:
    print("Inserting prompt...")
    expr = """(() => {
      const prompt = %s;
      const ta = document.querySelector('textarea[aria-label*="Chat"], textarea');
      const box = document.querySelector('div[contenteditable="true"][role="textbox"], div[contenteditable="true"]');
      const fire = (el) => {
        el.dispatchEvent(new InputEvent('input', {bubbles:true, inputType:'insertText', data: prompt}));
        el.dispatchEvent(new Event('change', {bubbles:true}));
      };
      if (box) { box.focus(); box.textContent = prompt; fire(box); }
      if (ta) { const setter = Object.getOwnPropertyDescriptor(window.HTMLTextAreaElement.prototype, 'value').set;
        setter.call(ta, prompt); ta.focus(); fire(ta); }
      const current = box ? box.innerText : (ta ? ta.value : '');
      return { ok: current === prompt };
    })()""" % json.dumps(text)
    result = evaluate(expr)
    if not result.get("ok"): raise RuntimeError(f"prompt insertion mismatch: {result}")
    print("Prompt inserted.")
    return result

def click_send() -> None:
    print("Clicking send...")
    result = evaluate("""(() => {
      const candidates = Array.from(document.querySelectorAll('button'));
      const send = candidates.find(b => /Send prompt/i.test(b.getAttribute('aria-label') || ''));
      if (!send) return {clicked:false};
      send.click();
      return {clicked:true};
    })()""")
    if not result.get("clicked"): raise RuntimeError("failed to submit prompt")
    print("Send clicked.")

def streaming() -> bool:
    return bool(evaluate("""Array.from(document.querySelectorAll('button')).some(b => /Stop|Cancel|streaming/i.test((b.getAttribute('aria-label') || '') + ' ' + (b.innerText || '')))"""))

def assistant_messages() -> list[dict]:
    raw = evaluate("""JSON.stringify(Array.from(document.querySelectorAll('[data-message-author-role="assistant"]')).map((e, i) => ({ index: i, text: e.innerText || '' })))""")
    return json.loads(raw or "[]")

def wait_for_final_message() -> list[dict]:
    print("Waiting for response...")
    deadline = time.time() + TIMEOUT_SECONDS
    while time.time() < deadline:
        last_messages = assistant_messages()
        is_streaming = streaming()
        if last_messages:
            last_msg = last_messages[-1].get("text", "").strip()
            if not is_streaming and last_msg:
                print("Response received.")
                return last_messages
            else:
                print(f"Still waiting... (msg length: {len(last_msg)})")
        else:
            print("No messages yet...")
        time.sleep(POLL_SECONDS)
    raise RuntimeError("timed out")

open_chatgpt()
set_prompt_exact(prompt)
click_send()
messages = wait_for_final_message()
RESULT_JSON.write_text(json.dumps({"assistant_text": messages[-1]["text"]}, indent=2))
print(f"DONE: Result saved to {RESULT_JSON}")
EOF
