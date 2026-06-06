#!/usr/bin/env python3
"""Google AI Mode driver for browser-harness. Env-var interface same as ChatGPT driver.

Usage:
    GOOGLE_AI_PROMPT_FILE=/tmp/prompt.txt GOOGLE_AI_RESULT_JSON=/tmp/result.json \\
    browser-harness -c "exec(open('tools/infra/google_ai_driver.py').read())"
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

# Find textarea and insert prompt
safe = json.dumps(prompt)  # JSON-escape the prompt
js(f"""
  var el = document.querySelector('textarea');
  if (!el) el = document.querySelector('input[type="text"]');
  if (!el) el = document.querySelector('[role="combobox"]');
  if (el) {{
    el.focus();
    el.value = {safe};
    el.dispatchEvent(new Event('input', {{bubbles: true}}));
    el.dispatchEvent(new Event('change', {{bubbles: true}}));
  }}
""")
time.sleep(0.5)

# Click send
js("""
  var btn = document.querySelector('button[aria-label*="Send"]');
  if (!btn) {
    var all = document.querySelectorAll('button');
    for (var i = 0; i < all.length; i++) {
      if (/Send|Submit/i.test(all[i].getAttribute('aria-label') || '')) { btn = all[i]; break; }
    }
  }
  if (btn) btn.click();
  else {
    var el = document.querySelector('textarea');
    if (el) el.dispatchEvent(new KeyboardEvent('keydown', {key:'Enter', code:'Enter', keyCode:13, bubbles:true}));
  }
""")

# Wait for response
timeout = int(os.environ.get("GOOGLE_AI_TIMEOUT_SECONDS", "120"))
stable = 0
last = ""
for _ in range(timeout // 3):
    time.sleep(3)
    body = js("return (document.body.innerText || '')")
    idx = body.find("AI Mode")
    if idx >= 0:
        tail = body[idx:idx+200]
    else:
        tail = body[-200:]
    if tail == last:
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
