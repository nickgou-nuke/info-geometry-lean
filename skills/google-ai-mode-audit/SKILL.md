---
name: google-ai-mode-audit
description: Use when submitting a repository architecture or literature audit to Google AI Mode through this repository's browser-harness lane, especially on Ubuntu ARM with Snap Chromium.
metadata:
  short-description: Submit and capture Google AI Mode audits
---

# Google AI Mode Audit

Use this skill for an explicitly requested external review through Google AI
Mode. It supplements the installed `browser-harness` skill with this
repository's routing and the Ubuntu ARM browser setup. It does not replace
source review or make Google AI output authoritative.

## Required route

- Read `docs/CANONICAL_AGENT_PIPELINE.md` for the current tool route.
- Use `scripts/google-ai-search.sh`, which runs the Google AI Mode lane through
  `browser-harness` and records the prompt and response in the agent message
  ledger.
- Keep Google AI Mode separate from aiClaw ChatGPT/Gemini queues. Do not send
  this request through `aiclaw_chat.py`.
- Use the exact artifact under review as the prompt context. Request a
  bounded audit with prioritized findings, supporting sources, and explicit
  uncertainty; distinguish suggestions from verified repository facts.

## Ubuntu ARM with Snap Chromium

On Ubuntu ARM, use the Ubuntu Chromium package. The browser-harness Snap
diagnostic recommends Google's amd64 `.deb`, which is not an ARM option.
Opening `chrome://inspect/#remote-debugging` alone does not provide the CDP
endpoint required by the harness.

When the existing Chromium session does not expose CDP, start a second
Chromium instance with a temporary, isolated profile. Set `DISPLAY` to the
active graphical display; `:1` is the observed display on the current host:

```bash
DISPLAY=:1 /snap/bin/chromium \
  --remote-debugging-port=9222 \
  --user-data-dir=/tmp/browser-harness-arm-chromium \
  --no-first-run about:blank
```

Keep that process running. Confirm it prints a `DevTools listening` URL, then
confirm browser-harness can see its tabs:

```bash
BU_CDP_URL=http://127.0.0.1:9222 browser-harness <<'PY'
print(list_tabs())
PY
```

The repo's Google script detects the CDP websocket at `127.0.0.1:9222` and
passes it to browser-harness. If using another port, set `BU_CDP_WS` to the
websocket URL reported by that port's `/json/version` endpoint before running
the script. Do not assume the Codex app's built-in browser is the same surface
as the host Chromium display.

The temporary profile is separate from the user's normal Chromium profile and
does not inherit its cookies. If Google requires sign-in, stop at the login
wall and let the user complete sign-in in that browser window; do not request
or handle their password or MFA.

## Submit and capture

For example, to audit the repository's Darwin pipeline blueprint:

```bash
./scripts/google-ai-search.sh --raw \
  "Audit the following pipeline blueprint. Identify the highest-priority architectural gaps, incorrect or unsupported claims, relevant primary literature, and concrete improvements. Distinguish Git ancestry, compiler observations, declaration fingerprints, InfoTree data, and inferred affinity. Treat repository claims as hypotheses to verify against the cited source inventory. Return concise findings with source links and uncertainty labels.\n\n$(cat docs/DARWIN_PIPELINE_BLUEPRINT.md)"
```

The script's send action clicks an enabled Google AI Mode send/search button;
it does not press Enter as a fallback. If the page has no input or enabled
send button, or the response is not captured, report the lane as incomplete.
Do not claim the audit was submitted until the script returns a captured
response.

## Evidence boundary

Google AI Mode is an external reviewer, not an implementation or proof
authority. Preserve its response as an audit artifact, inspect its citations,
and verify repository-specific claims against current source. For Lean claims,
the owner file and kernel-checked build remain authoritative. Do not turn
generated suggestions into source edits without ordinary review and local
verification.
