# Browser Harness Instantiation & Driver Runbook

> **Canonical Guide for Live CDP Browser Harness Instantiation**  
> Audited: 2026-07-21  
> Scope: Ubuntu Linux (Snap Chromium & Google Chrome) + `browser-harness` + ChatGPT Pro CDP Integration

---

## 🏛️ Executive Summary

This runbook documents the **exact, reproducible 5-step procedure** to launch a visible GUI Chrome/Chromium browser window, expose the Chrome DevTools Protocol (CDP) WebSocket endpoint on port `9222`, and instantiate `browser-harness` for live Socratic Oracle interaction.

---

## 🛠️ Step 1: Tool Installation & Environment Setup

Install or upgrade `browser-harness` using `uv` (Python 3.12 runtime):

```bash
# 1. Install/Upgrade browser-harness
uv tool install --python 3.12 --upgrade --force browser-harness

# 2. Disable telemetry & auto-recordings
browser-harness telemetry disable
```

---

## 🌐 Step 2: Launch Visible GUI Chrome with CDP Debugging

On Ubuntu Linux (specifically Snap Chromium), launching Chrome with `--remote-debugging-port` requires explicit `--user-data-dir` and `--remote-allow-origins=*` flags to prevent snap sandbox socket isolation.

Execute the launch command:

```bash
# Launch Chromium GUI on DISPLAY=:0 with port 9222 enabled
DISPLAY=${DISPLAY:-:0} /snap/bin/chromium \
  --user-data-dir="$HOME/.config/chrome_gui_dev_profile" \
  --remote-debugging-port=9222 \
  --remote-allow-origins=* \
  "https://chatgpt.com/?temporary-chat=true" > /tmp/chromium_launch.log 2>&1 &
```

> [!IMPORTANT]
> - `--user-data-dir` isolates dev profile settings from default desktop profile locks.
> - `--remote-allow-origins=*` allows local WebSocket handshakes from `browser-harness`.

---

## 🔍 Step 3: Fetch Active CDP WebSocket URL

Query `http://127.0.0.1:9222/json/version` to extract the live `webSocketDebuggerUrl`:

```bash
curl -s http://127.0.0.1:9222/json/version
```

**Expected JSON Output**:
```json
{
   "Browser": "Chrome/150.0.7871.100",
   "Protocol-Version": "1.3",
   "User-Agent": "Mozilla/5.0 ...",
   "webSocketDebuggerUrl": "ws://127.0.0.1:9222/devtools/browser/3bbef91d-97a6-4d89-86f2-b65b502c8ea9"
}
```

Extract the `webSocketDebuggerUrl` string into environment variable `BU_CDP_WS`.

---

## ⚡ Step 4: Verify Connection via `browser-harness`

Test page connectivity by running `page_info()` via `browser-harness` stdin:

```bash
export BU_CDP_WS="ws://127.0.0.1:9222/devtools/browser/<UUID>"

browser-harness <<'PY'
print("PAGE INFO:")
print(page_info())
PY
```

**Successful Output**:
```python
{'url': 'https://chatgpt.com/', 'title': 'ChatGPT: Chat, Work, Create & Code with AI', 'w': 1920, 'h': 924}
```

---

## 🤖 Step 5: Execute Prompt Submission & Response Capture

Use the Python DOM injection script to target `#prompt-textarea`, trigger input events, and submit to ChatGPT Pro:

```bash
BU_CDP_WS="ws://127.0.0.1:9222/devtools/browser/<UUID>" browser-harness <<'PY'
import time, json

prompt = """You are a Socratic Oracle Referee auditing a formalization in Lean 4.

Hypothesis: Bost-Connes Partition Function Divergence
Rationale: Harmonic series non-summability at beta = 1 forces phase transition across UHF colimit.
Apex: InfoGeometry.Canonical.BCPartitionFunction.bc_partition_divergence_at_one

Please audit this formal intent and provide your verdict (BREAKTHROUGH / MINOR / REJECT) with a one-line mathematical rationale."""

# 1. Insert prompt text
expr = f"""(() => {{
  const el = document.querySelector('#prompt-textarea') || document.querySelector('div[contenteditable="true"]');
  if (!el) return {{ ok: false, reason: "no input area" }};
  el.focus();
  el.innerHTML = '<p>' + {json.dumps(prompt)}.replace(/\\n/g, '<br>') + '</p>';
  el.dispatchEvent(new InputEvent('input', {{ bubbles: true, inputType: 'insertText' }}));
  return {{ ok: true }};
}})()"""
js(expr)

# 2. Click send button
submit_expr = """(() => {
  const btn = document.querySelector('button[data-testid="send-button"]') || document.querySelector('#composer-submit-button') || document.querySelector('button[aria-label="Send prompt"]') || document.querySelector('button[aria-label="Send message"]');
  if (btn) { btn.click(); return { ok: true }; }
  return { ok: false };
})()"""
js(submit_expr)

# 3. Wait for response generation
time.sleep(15)

# 4. Read response text
read_expr = """(() => {
  const articles = Array.from(document.querySelectorAll('article'));
  if (articles.length > 0) return { ok: true, text: articles[articles.length - 1].innerText };
  return { ok: true, text: document.body.innerText.slice(-800) };
})()"""

out = js(read_expr)
print("ORACLE RESPONSE:", out.get("text"))
PY
```

---

## 🩺 Diagnostics & Troubleshooting

Run the doctor script anytime to verify process health:

```bash
browser-harness --doctor
```

**Healthy Diagnostic State**:
```text
browser-harness doctor
  platform          Linux
  version           0.1.6
  [ok  ] chrome running
  [ok  ] daemon alive
  [ok  ] active browser connections — 1
```
