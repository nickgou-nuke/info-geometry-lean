#!/usr/bin/env python3
import sys
from pathlib import Path
REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

import subprocess
import argparse
import json
import time

from tools.infra.lean_audit_prompt import build_repair_prompt
from tools.infra.chatgpt_lane_guard import browser_chatgpt_lane

try:
    from tools.infra.agent_message_ledger import record_message
except Exception:  # pragma: no cover - observation must never block bridge use.
    record_message = None

def ask_chatgpt(prompt_text):
    prompt_text = build_repair_prompt(
        "ChatGPT collaborator query:\n\n" + prompt_text,
    )
    prompt_path = Path("/tmp/chatgpt_prompt.txt")
    prompt_path.write_text(prompt_text, encoding="utf-8")
    
    harness_script = """
import json
import time
with open('/tmp/chatgpt_prompt.txt', 'r') as f:
    text = f.read()

safe_prompt = json.dumps(text)

# Use the currently active tab where the user is already logged in and ready.
# The outer Python process holds the repo queue while this harness runs.
ensure_real_tab()

def page_state():
    return js('''
    (() => {
      const buttons = Array.from(document.querySelectorAll('button'));
      const buttonText = b => (b.getAttribute('aria-label') || '') + ' ' + (b.innerText || '') + ' ' + (b.getAttribute('data-testid') || '');
      const streaming = buttons.some(b => /Stop answering|Stop generating|Stop|Cancel|streaming/i.test(buttonText(b)));
      const fields = Array.from(document.querySelectorAll('textarea[aria-label*="Chat"], textarea, div[contenteditable="true"][role="textbox"], div[contenteditable="true"], #prompt-textarea'));
      const composerLengths = fields.map(el => {
        const text = el.tagName === 'TEXTAREA' ? el.value : (el.innerText || el.textContent || '');
        return text.length;
      });
      return {streaming, composerLengths, assistantCount: document.querySelectorAll('[data-message-author-role="assistant"]').length};
    })()
    ''')

state = page_state()
if state.get('streaming'):
    raise RuntimeError('CHATGPT_LANE_BUSY: visible Stop/Cancel/streaming control is present')
if any(int(n) > 0 for n in (state.get('composerLengths') or [])):
    raise RuntimeError(f'CHATGPT_COMPOSER_NOT_EMPTY: composer_lengths={state.get("composerLengths")}')

assistant_count_before = int(state.get('assistantCount') or 0)

# Target the main chat input
# ChatGPT uses a contenteditable div
inserted = js(f'''
(() => {{
  const prompt = {safe_prompt};
  const el = document.getElementById("prompt-textarea") ||
    document.querySelector('div[contenteditable="true"][role="textbox"], div[contenteditable="true"], textarea');
  if (!el) return {{ok:false, reason:'prompt_field_missing'}};
  el.focus();
  if (el.tagName === 'TEXTAREA') {{
    const setter = Object.getOwnPropertyDescriptor(window.HTMLTextAreaElement.prototype, 'value').set;
    setter.call(el, prompt);
  }} else {{
    el.textContent = prompt;
  }}
  el.dispatchEvent(new InputEvent("input", {{ bubbles: true, inputType: "insertText", data: prompt }}));
  el.dispatchEvent(new Event("change", {{ bubbles: true }}));
  const current = el.tagName === 'TEXTAREA' ? el.value : (el.innerText || el.textContent || '');
  return {{ok: current === prompt, length: current.length}};
}})()
''')
if not inserted.get('ok'):
    raise RuntimeError(f'prompt insertion failed: {inserted}')

deadline = time.time() + 10
clicked = {'ok': False, 'reason': 'not_started'}
while time.time() < deadline:
    state = page_state()
    if state.get('streaming'):
        raise RuntimeError('CHATGPT_LANE_BUSY: generation started before click confirmation')
    clicked = js('''
    (() => {
      const btn = Array.from(document.querySelectorAll('button')).find(b =>
        !b.disabled && (/send-button/i.test(b.getAttribute('data-testid') || '') ||
          /Send/i.test((b.getAttribute('aria-label') || '') + ' ' + (b.innerText || ''))));
      if (!btn) return {ok:false, reason:'send_button_missing', state: %s};
      btn.click();
      return {ok:true};
    })()
    ''' % json.dumps(state))
    if clicked.get('ok'):
        break
    wait(0.5)
if not clicked.get('ok'):
    raise RuntimeError(f'failed to submit prompt: {clicked}')

# Wait for the generation to complete.
print("Waiting for generation to finish...")
deadline = time.time() + 180
last_text = ''
while time.time() < deadline:
    state = page_state()
    last_text = js('''
    (() => {
      const responses = document.querySelectorAll('[data-message-author-role="assistant"]');
      if (responses.length === 0) return '';
      return responses[responses.length - 1].innerText || responses[responses.length - 1].textContent || '';
    })()
    ''')
    if (
        int(state.get('assistantCount') or 0) > assistant_count_before and
        not state.get('streaming') and
        last_text.strip()
    ):
        break
    wait(1)
else:
    raise RuntimeError('timed out waiting for final assistant message')

# Extract the last assistant message
script = '''
var responses = document.querySelectorAll('[data-message-author-role="assistant"]');
if (responses.length > 0) {
    responses[responses.length - 1].innerText;
} else {
    "ERROR: Could not extract response from the DOM.";
}
'''
response_text = js(script)
print("--- CHATGPT RESPONSE ---")
print(response_text)
"""
    started = time.monotonic()
    output = ""
    error = ""
    success = False
    try:
        with browser_chatgpt_lane(
            source="chatgpt_collaborator_bridge",
            platform="chatgpt",
            prompt_chars=len(prompt_text),
            reason="legacy_collaborator_browser_harness",
        ):
            result = subprocess.run(
                ["browser-harness"],
                input=harness_script,
                capture_output=True,
                text=True,
                check=True
            )
        output = result.stdout or ""
        success = True
        return output
    except subprocess.CalledProcessError as e:
        error = e.stderr or str(e)
        print(f"Browser harness failed to communicate with ChatGPT: {e.stderr}", file=sys.stderr)
        return None
    except Exception as exc:
        error = str(exc)
        print(f"Browser harness failed to communicate with ChatGPT: {error}", file=sys.stderr)
        return None
    finally:
        if record_message is not None:
            try:
                record_message(
                    source_tool="chatgpt_collaborator_bridge.py",
                    source_file="tools/infra/chatgpt_collaborator_bridge.py",
                    channel="chatgpt_collaborator_browser",
                    provider="browser-harness",
                    model="chatgpt",
                    platform="chatgpt",
                    prompt_text=prompt_text,
                    response_text=output or error,
                    success=success,
                    latency_ms=(time.monotonic() - started) * 1000.0,
                    metadata={"failure_pattern": error},
                )
            except Exception:
                pass

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Delegate a complex auditing task to ChatGPT via Browser Harness.")
    parser.add_argument("prompt", help="The prompt or code to send to ChatGPT")
    args = parser.parse_args()
    
    response = ask_chatgpt(args.prompt)
    if response:
        print(response)
