# Browser Harness Usage in info-geometry-lean

> Status: operational-doc
> Verified: 2026-07-21

This file records the verified local browser-harness surface for this repo.
It covers install/help verification, repo-specific Google AI Mode search,
single-flight ChatGPT lane discipline, and where to extend with custom
helpers.

## 1. Verified Install State

- installed package: browser-harness 0.1.6
- companion package: browser-use 0.13.6
- global command: `/home/goutev/.local/bin/browser-harness`
- package module: `browser_harness` from site-packages
- editable source tree available at: `/home/goutev/Developer/browser-harness`

Verify yourself:

```bash
browser-harness --version
browser-harness --help
```

Current help surface:

```text
Browser Harness

Read SKILL.md for the default workflow and examples.

Typical usage:
  browser-harness <<'PY'
  ensure_real_tab()
  print(page_info())
  PY

Commands:
  browser-harness --version        print the installed version
  browser-harness --doctor         diagnose install, daemon, and browser state
  browser-harness doctor           same as --doctor
  browser-harness auth login       sign in to Browser Use Cloud for cloud browsers
  browser-harness auth status      show Browser Use Cloud auth state
  browser-harness recordings       show recording status and recent sessions
  browser-harness recordings --latest   print the newest recording directory
  browser-harness recordings enable     save browser actions locally by default
  browser-harness recordings disable    stop saving browser actions by default
  browser-harness skill            print the browser-harness skill text
  browser-harness --update [-y]    pull the latest version
  browser-harness --reload         stop the daemon so next call picks up code changes
```

## 2. Diagnostics

Run:

```bash
browser-harness doctor
browser-harness --doctor
```

Interpretation:

- `chrome running` ok → Chrome/Chromium was detected.
- `daemon alive` fail → fix Chrome remote-debugging permission first.
- `active browser connections` 0 → no live harness session attached.
- `Browser Use cloud auth` fail → local-only flow still works.

If local Chrome misses remote debugging:

- open `chrome://inspect/#remote-debugging`
- tick "Allow remote debugging for this browser instance"
- click Allow on the Chrome 144+ popup if it appears
- retry `page_info()`

## 2a. Ubuntu Chromium CDP Session (Verified 2026-10-29)

Ubuntu Chromium is the working local browser for this machine. From the active
Ubuntu desktop session, start it with the same CDP port used by the harness:

```bash
chromium --remote-debugging-port=9222 &
```

If the shell does not inherit `DISPLAY`, inspect `/tmp/.X11-unix/` and set
`DISPLAY` to the active display socket (for example, `DISPLAY=:1` when the
active socket is `X1`). Do not launch a second browser if port `9222` is
already occupied; query the existing endpoint first:

```bash
curl --noproxy '*' -sS http://127.0.0.1:9222/json/version
```

Attach with the documented stdin interface and an explicit local CDP endpoint:

```bash
BU_CDP_URL=http://127.0.0.1:9222 browser-harness <<'PY'
print(page_info())
PY
```

To inspect a shared page, navigate through the attached browser so it uses that
browser profile's existing Google session:

```bash
BU_CDP_URL=http://127.0.0.1:9222 browser-harness <<'PY'
url = "https://aistudio.google.com/app/prompts/..."
new_tab(url)
wait_for_load()
print(page_info())
print(js("document.body.innerText"))
PY
```

The default `browser-harness --doctor` checks only the browser visible in its
own execution context. In the managed agent shell, run browser-harness through
the approved local-browser access route; a sandbox-local `chrome running`
failure does not establish that the desktop Chromium session is absent. On
2026-10-29 the local daemon log recorded a successful attach to port 9222 and a
later connection loss; reconnecting with the explicit `BU_CDP_URL` and stdin
interface returned the active Chromium tab.

## 3. Basic CLI Usage

Repo-standard direct invocation:

```bash
browser-harness -c '
ensure_real_tab()
page = page_info()
print(page)
'
```

Notes:

- first navigation should be `new_tab(url)`, not `goto_url(url)`.
- CDP helpers are preimported.
- If code changed in an editable checkout, run `browser-harness --reload`.

## 4. Google AI Mode Search

This repo uses a browser-harness Google AI lane backed by local Chrome.

Primary entrypoint:

```bash
cd /home/goutev/repos/info-geometry-lean
./scripts/google-ai-search.sh "Bost Connes KMS state Cuntz algebra O_2"
```

Implementation notes:

- `scripts/google-ai-search.sh` does not use aiClaw.
- It prepends the Google AI prompt to the repo `google_ai_driver.py` and runs
  it through the installed `browser-harness` CLI.
- Results are recorded via `tools/infra/agent_message_ledger.py` under
  channel `google_ai_browser_harness_lane`.

Required helpers in this repo:

- `tools/infra/google_ai_driver.py`
- `tools/infra/google_ai_searcher.py`
- `tools/infra/agent_message_ledger.py`

Environment:

- `BU_CDP_WS` optional. If omitted, `google-ai-search.sh` auto-detects the
  local CDP websocket from `http://127.0.0.1:9222/json/version`.
- `GOOGLE_AI_TIMEOUT_SECONDS` or `GOOGLE_AI_SEARCH_TIMEOUT` controls wait.

## 5. ChatGPT Single-Flight Lane Discipline

Per repo policy, all ChatGPT browser automation must respect single-flight
queue state.

Status + recovery:

```bash
python3 tools/infra/aiclaw_chat.py queue-status --platform chatgpt
```

Send one prompt:

```bash
python3 tools/infra/aiclaw_chat.py prompt \
  --platform chatgpt \
  --prompt "Your prompt text here"
```

Release the lane after review:

```bash
python3 tools/infra/aiclaw_chat.py queue-release \
  --platform chatgpt \
  --reason final_visible_answer_recorded
```

Prune stale active markers if needed:

```bash
python3 tools/infra/aiclaw_chat.py queue-prune-active --platform chatgpt
```

## 6. Python Guard Usage

Wrap direct browser-harness script work with the shared ChatGPT guard:

```python
from tools.infra.chatgpt_lane_guard import browser_chatgpt_lane

with browser_chatgpt_lane(source="my_script", platform="chatgpt"):
    # browser-harness operations here
    pass
```

Normal completion releases the lane.
An exception leaves `busy.json` in place so the final browser answer can be
recovered read-only before reuse.

## 7. Extending Helpers

Task-specific additions belong in repo-local tooling, not core harness code.

- repo-local harness support: `tools/infra/`
- repo-local browser drivers: `tools/infra/google_ai_driver.py`,
  `tools/infra/google_ai_searcher.py`
- repo-local ledgers: `tools/infra/agent_message_ledger.py`

If you need a new browser helper, add it under `tools/infra/` and invoke it
from a thin `browser-harness -c` script or bash wrapper.

## 8. Operational Rules

- No loop popups: do not spawn unauthenticated Chrome GUI windows in loops.
- Kernel supremacy: browser-retrieved material is observation only.
  Mathematical claims require Lean 4 kernel verification via `lake build`.
- Single-flight first: never send another ChatGPT prompt when the lane is busy.
- Keep recording consent defaults conservative; enable only after explicit yes.
