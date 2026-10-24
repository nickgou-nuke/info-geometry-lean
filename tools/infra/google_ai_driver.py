#!/usr/bin/env python3
"""Google AI Mode driver for browser-harness. Env-var interface same as ChatGPT driver.

Usage:
    GOOGLE_AI_PROMPT_FILE=/tmp/prompt.txt GOOGLE_AI_RESULT_JSON=/tmp/result.json \\
    browser-harness <<'PY'
    exec(open('tools/infra/google_ai_driver.py').read())
    PY
"""
from pathlib import Path
import json, os, time

PROMPT_FILE = Path(os.environ.get("GOOGLE_AI_PROMPT_FILE", ""))
RESULT_JSON = Path(os.environ.get("GOOGLE_AI_RESULT_JSON", "/tmp/google_ai_result.json"))
SENTINEL = "/tmp/google_ai_tab_ready"

if not PROMPT_FILE.exists():
    raise RuntimeError("GOOGLE_AI_PROMPT_FILE must point to an existing prompt file")

prompt = PROMPT_FILE.read_text(encoding="utf-8")

# Open or reuse tab
if os.path.exists(SENTINEL):
    current = js("return window.location.href;")
    if "google.com/ai" not in current:
        goto_url("https://google.com/ai")
        wait_for_load()
        time.sleep(1)
else:
    new_tab("https://google.com/ai")
    wait_for_load()
    time.sleep(2)
    open(SENTINEL, "w").close()

before_text = js("return (document.body.innerText || '')")

# Find textarea / contenteditable / combobox and insert prompt via native setter or execCommand
safe = json.dumps(prompt)  # JSON-escape the prompt
inserted = js(f"""(() => {{
  const text = {safe};
  const el = document.querySelector('textarea')
    || document.querySelector('div[contenteditable="true"][role="textbox"]')
    || document.querySelector('div[contenteditable="true"]')
    || document.querySelector('input[type="text"]')
    || document.querySelector('[role="combobox"]');
  if (!el) return {{ ok: false, reason: 'no-input-element' }};
  el.focus();
  if (el.tagName === 'TEXTAREA' || el.tagName === 'INPUT') {{
    const proto = el.tagName === 'TEXTAREA'
      ? window.HTMLTextAreaElement.prototype
      : window.HTMLInputElement.prototype;
    const desc = Object.getOwnPropertyDescriptor(proto, 'value');
    if (desc && desc.set) {{
      desc.set.call(el, text);
    }} else {{
      el.value = text;
    }}
  }} else {{
    document.execCommand('selectAll', false);
    document.execCommand('delete', false);
    document.execCommand('insertText', false, text);
  }}
  el.dispatchEvent(new InputEvent('input', {{ bubbles: true, inputType: 'insertText', data: text }}));
  el.dispatchEvent(new Event('change', {{ bubbles: true }}));
  return {{ ok: true, tag: el.tagName }};
}})()""")
if not isinstance(inserted, dict) or not inserted.get("ok"):
    raise RuntimeError(f"Google AI Mode input field not found: {inserted}")
time.sleep(0.5)

# Click send (or submit form if button uses Search/Submit/Send aria-label)
sent = js("""
  var buttons = Array.from(document.querySelectorAll('button, [role="button"]'));
  var btn = buttons.find(function(b) {
    var label = (b.getAttribute('aria-label') || '') + ' ' + (b.getAttribute('title') || '') + ' ' + (b.innerText || '');
    return /Send|Submit|Ask|Search AI/i.test(label) && !b.disabled && b.offsetParent !== null;
  });
  if (!btn) {
    btn = document.querySelector('button[type="submit"]:not([disabled])');
  }
  if (!btn) return 'no-enabled-send-button';
  btn.click();
  return 'sent';
""")
if sent != "sent":
    raise RuntimeError("Google AI Mode has no enabled Send/Submit button")

# Wait for response
def _is_intermediate(text: str) -> bool:
    tail = text[-2000:].lower()
    return any(
        marker in tail
        for marker in (
            "thinking a little longer",
            "thinking...",
            "generating",
            "searching",
        )
    )

def _clean_summary(text: str) -> str:
    skipped = {
        "thinking a little longer",
        "thinking...",
        "generating",
        "searching",
    }
    lines = []
    for line in text.splitlines():
        if line.strip().lower() in skipped:
            continue
        lines.append(line)
    return "\n".join(lines).strip()

timeout = int(os.environ.get("GOOGLE_AI_TIMEOUT_SECONDS", "120"))
stable = 0
last = ""
prompt_need = prompt.strip()[:160]
started = time.monotonic()
for _ in range(timeout // 3):
    time.sleep(3)
    body = js("return (document.body.innerText || '')")
    prompt_idx = body.find(prompt_need) if prompt_need else 0
    response_region = body[prompt_idx:] if prompt_idx >= 0 else body
    if (
        prompt_idx >= 0
        and not _is_intermediate(body)
        and (
            "AI responses may include mistakes" in response_region
            or "AI Mode response is ready" in response_region
        )
        and time.monotonic() - started >= 8
    ):
        break
    idx = body.find("AI Mode")
    if idx >= 0:
        tail = body[idx:idx+200]
    else:
        tail = body[-200:]
    if tail == last and not _is_intermediate(body):
        stable += 1
        if stable >= 3:
            break
    else:
        stable = 0
        last = tail

# Extract full response
time.sleep(1)
body = js("return (document.body.innerText || '')")
idx = body.find("AI Mode")
if idx == -1:
    idx = body.find("Gemini")
result = {"summary": body[idx:idx+6000] if idx >= 0 else body[:6000], "links": []}
result["summary"] = _clean_summary(result["summary"])

# Extract links
raw = js("""JSON.stringify(
  Array.from(document.querySelectorAll('a[href^="http"]'))
    .filter(function(a) { var t = (a.innerText||'').trim(); return t.length > 10 && a.href.indexOf('google.com') === -1; })
    .slice(0, 10)
    .map(function(a) { return {title: (a.innerText||'').trim().slice(0,150), url: a.href}; })
)""")
try:
    result["links"] = json.loads(raw)
except:
    pass

RESULT_JSON.write_text(json.dumps(result), encoding="utf-8")
print(f"Google AI: {len(result['summary'])} chars, {len(result['links'])} links")
