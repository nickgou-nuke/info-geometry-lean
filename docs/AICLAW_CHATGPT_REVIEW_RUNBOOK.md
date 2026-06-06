# aiClaw ChatGPT Review Runbook

> Status: `maintained local guide`
> Scope: aiClaw/localBridge ChatGPT proof-review lane, SymPy witness lane, and
> read-only browser recovery.
> Authority: Lean source and `lake env lean` remain proof authority. aiClaw,
> ChatGPT, SymPy, Arango, and browser DOM state are evidence or review aids.

This document records the process used to call ChatGPT through aiClaw without
stacking prompts on top of each other, how status is polled, how final output is
distinguished from the observed `Thinking` intermediate payload, and what can
and cannot be recovered afterwards.

For Lean proof-repair use, trigger the local skill:

- `skills/socratic-oracle-proof-repair/SKILL.md`

That skill defines the Socratic proof-auditor loop: send the complete owner
file plus all relevant build errors in one prompt, wait for the final visible
answer, request one complete corrected Lean file, and accept only
kernel-checked source edits performed by the coding agent.

The external formal precedent for the adversarial-dialogue shape is documented
in:

- `docs/DEBATE_ORACLE_CONVERGENCE_MAP.md`

That map records the verified split: `external_refs/deepmind-debate` proves
finite stochastic debate correctness against adversarial Eve, while
`external_refs/lean-stat-learning-theory/SLT/ConvergenceL1Subseq.lean` proves a
separate analytic `L1` subsequence convergence theorem. Do not merge those into
an unproved "chatbot convergence" claim.

## Hard Boundaries

- Do not send a second prompt while a first prompt may still be generating.
- Do not write aiClaw proof memory into the repo theorem-DAG Arango brain.
- Do not treat SymPy witnesses as Lean proof authority.
- Do not treat ChatGPT prose as theorem authority.
- Do not confuse ChatGPT with the coding agent. ChatGPT is an external auditor
  and repair suggester; the coding agent owns file edits and verification.
- Do not send secrets or full unfiltered repo dumps through the ChatGPT web UI.
- Do not claim to recover private model chain-of-thought.

The recoverable material is:

- explicit user prompts sent through aiClaw
- final assistant text visible in the ChatGPT page DOM
- aiClaw REST payloads
- browser tab/login status
- visible DOM generation indicators
- local tool logs and generated artifacts

The unrecoverable material is private model reasoning. If the model generated
hidden reasoning internally, neither aiClaw nor DevTools exposes it as an
auditable artifact. Record an observable event trace instead.

## Components

The local aiClaw client code lives under:

- `aihub/localBridge/clawBotCli/clawbot/transport/ai_api.py`
- `aihub/localBridge/clawBotCli/clawbot/services/ai_chat.py`
- `aihub/localBridge/clawBotCli/clawbot/domain/ai_parsers.py`

The ChatGPT DOM adapter lives under:

- `aihub/aiClaw/src/adapters/chatgpt-adapter.ts`

The repo wrapper added for controlled operation is:

- `tools/infra/aiclaw_chat.py`
- `tools/infra/chatgpt_lane_guard.py` for direct browser-harness senders that
  must share the same `tmp/aiclaw_queue/<platform>/busy.json` lane marker.
- `tools/infra/socratic_clawbot.py` for Lean owner-file oracle prompts; this
  delegates transport to `aiclaw_chat.py`.
- `tools/infra/socratic_oracle_prompt_gepa.py` for archive-first GEPA-style
  prompt-profile evaluation. It does not send prompts and does not replace the
  stable default unless empirical archived outcomes justify it.
- `tools/infra/socratic_oracle_record_outcome.py` for recording post-replacement Lean
  verification outcomes into the GEPA event archive.
- `tools/quality/oracle_prompt_regression_gate.py` for rejecting prompt-profile
  regressions before deployment.

The isolated proof-memory Arango wrapper is:

- `tools/infra/aiclaw_auto_arango.py`

The SymPy/Lean pipeline wrappers are:

- `tools/infra/auto_sympy_witnesses.py`
- `tools/infra/auto_proof_pipeline.py`

## Extension Log Semantics

The browser console contains two related names:

- `aiClaw`: the extension client connected to the LocalBridge WebSocket.
- `aiClaw-BG`: the extension background dispatcher that sends an execute task
  into the target browser tab.

Lines like these mean a server-side task was dispatched into the ChatGPT tab:

```text
[aiClaw] received message: request.execute_task
[aiClaw] handling request.execute_task, taskId: task_api_...
[aiClaw-BG] Dispatching task ... to tab ... (chatgpt)
```

The local Python queue in `aiclaw_chat.py` only serializes callers that use
that adapter.  It does not automatically serialize:

- direct `browser-harness` scripts;
- manual browser actions;
- other agents calling the extension/server directly;
- old scripts that submit prompts through their own DOM code.

Therefore all repo-owned ChatGPT senders must use one of these routes:

- `tools/infra/aiclaw_chat.py ask`
- `tools/infra/socratic_clawbot.py`
- a browser-harness script wrapped by `tools/infra/chatgpt_lane_guard.py`

Legacy direct routes are not safe unless they have been explicitly rewired to
one of those guards.  In this repo that means `ask_chatgpt_compiler` must call
`aiclaw_chat.py` rather than the old port-1956 WebSocket bridge, and
`chatgpt_collaborator_bridge.py` must hold `chatgpt_lane_guard.py` while the
browser-harness process is alive.

Direct browser-harness senders must also inspect the DOM before sending and
refuse to send if either condition is true:

- a visible `Stop answering`, `Stop generating`, `Cancel`, or streaming control
  is present;
- the composer is non-empty.

Do not use keyboard `Enter` as a fallback for a missing send button.  A missing
send button means the input was not recognized or the tab is busy; the correct
behavior is to fail and keep the lane held for read-only recovery.

If the console shows many `request.execute_task` / `aiClaw-BG Dispatching task`
lines while ChatGPT is still thinking, treat the tab as contaminated.  Do not
attribute the next visible answer to the current proof task until the prompt
hash, visible user prompt, and final assistant message have all been matched.

## aiClaw REST Contract

The repo-local `AIApiTransport` maps the AI operations to these localBridge
endpoints:

```text
GET  /api/v1/ai/status
POST /api/v1/ai/navigate
POST /api/v1/ai/new_conversation
POST /api/v1/ai/message
```

`/api/v1/ai/status` is a readiness endpoint, not a generation-progress
endpoint. It reports platform tab state:

```json
{
  "platforms": {
    "chatgpt": {
      "hasTab": true,
      "isLoggedIn": true
    }
  },
  "tabs": [
    {
      "active": true,
      "platform": "chatgpt",
      "tabId": 192411319,
      "url": "https://chatgpt.com/?temporary-chat=true"
    }
  ]
}
```

The readiness fields mean:

- `hasTab`: a browser tab matching the platform URL pattern exists.
- `isLoggedIn`: aiClaw has detected credentials/login state for that platform.
- `tabs[].active`: browser active tab state, not model generation state.
- `tabs[].tabId`: browser tab ID from the extension side.
- `tabs[].url`: current page URL.

The send endpoint returns an `AIMessageResult` parsed from raw JSON:

```json
{
  "success": true,
  "content": "Thinking",
  "conversation_id": null,
  "platform": "chatgpt",
  "raw": {
    "content": "Thinking",
    "durationMs": 20260,
    "executedAt": "2026-06-06T10:33:15.554Z",
    "platform": "chatgpt",
    "success": true,
    "taskId": "task_api_67a4f5b8"
  }
}
```

Observed rule: `content: "Thinking"` is not a reliable final answer even when
`success` is true. Treat it as an intermediate or extraction failure sentinel.

Also observed: the returned `taskId` did not exist under the generic localBridge
task API:

```text
GET /api/v1/tasks/task_api_67a4f5b8
-> {"code":"NOT_FOUND","detail":"task task_api_67a4f5b8 not found","error":"NOT_FOUND"}
```

Therefore do not poll `/api/v1/tasks/{taskId}` for ChatGPT message completion
unless the aiClaw server code is changed to store AI tasks there.

## Controlled Send Procedure

Use this order:

1. Check platform readiness.
2. Optionally start a new conversation.
3. Send exactly one prompt containing the complete owner file and all relevant
   build errors for the stuck proof.
4. If the result is final text, record it.
5. If the result is `Thinking` or otherwise suspect, do not send again.
6. Recover the visible final assistant message read-only from the browser DOM.

Commands:

```bash
python3 tools/infra/aiclaw_chat.py status
python3 tools/infra/aiclaw_chat.py queue-status --platform chatgpt
python3 tools/infra/aiclaw_chat.py wait --wait-timeout 30 --interval 1 --quiet
python3 tools/infra/aiclaw_chat.py ask --dry-run --prompt "$PROMPT"
python3 tools/infra/aiclaw_chat.py ask --wait --new --json --prompt "$PROMPT"
```

`ask` uses the local single-flight platform queue by default. The queue is a
per-platform file-backed lane under `tmp/aiclaw_queue`. It serializes concurrent
agents so one complete prompt packet is serviced at a time. If aiClaw returns
`Thinking`, times out after the prompt may have been sent, or otherwise returns
a suspect post-send result, the lane remains held by `busy.json` until the
visible final answer has been recovered and recorded. Release it only after
readback:

```bash
python3 tools/infra/aiclaw_chat.py queue-release \
  --platform chatgpt \
  --reason final_visible_answer_recorded
```

For proof-repair owner files, prefer:

```bash
python3 tools/infra/socratic_clawbot.py \
  --file lean/InfoGeometry/Canonical/BraidColimitZornBarrier.lean \
  --theorem zorn_maximal_fusion_subset \
  --dry-run --json
```

The fused wrapper runs the local Lean preflight, builds the complete-owner-file
prompt, and uses `aiclaw_chat.py` for dry-run, secret refusal, wait, new-chat,
single-flight queueing, and one-prompt send behavior.

The oracle prompt asks for canonical output:

````text
### Cause
...

### Replacement
```lean4
-- full corrected Lean file content
```

### API
...
````

Do not ask the chatbot for a diff hunk or theorem fragment. The replacement is
the whole corrected `.lean` file. This file-in/file-out contract is more robust
against collapsed whitespace, missing context, and partial line edits. Keep the
corrected file small and mathlib-style: minimal imports, cohesive owner scope,
short local helper lemmas, no architecture expansion.

`--dry-run` prints send metadata and does not contact aiClaw. Use it before
large prompts.

Optional additive prompt profiles live in:

```text
configs/oracle_prompt_profiles
```

They are opt-in:

```bash
python3 tools/infra/socratic_clawbot.py \
  --file lean/InfoGeometry/Canonical/BraidColimitZornBarrier.lean \
  --theorem zorn_maximal_fusion_subset \
  --prompt-profile debate_metric \
  --dry-run --json
```

The built-in prompt remains the default. Do not replace it from a GEPA result
unless archived proof-repair outcomes pass the regression gate.

Run archive-first prompt GEPA:

```bash
python3 tools/infra/socratic_oracle_prompt_gepa.py \
  --archive artifacts/oracle \
  --generations 2 \
  --population 8 \
  --json-out artifacts/oracle_gepa/latest.json \
  --md-out artifacts/oracle_gepa/latest.md

python3 tools/quality/oracle_prompt_regression_gate.py \
  artifacts/oracle_gepa/latest.json \
  --allow-keep-builtin
```

The GEPA scorer uses smoothed empirical proof-repair success rates when present.
Without enough archived verification outcomes it recommends `keep_builtin`.

After inserting a replacement from an oracle response, record the empirical
outcome:

```bash
python3 tools/infra/socratic_oracle_record_outcome.py \
  --event-json artifacts/oracle/zorn_maximal_fusion_subset.json
```

The recorder reruns `lake env lean` on the owner file from the event, writes a
`verification` block, and archives the event under
`quarantine/oracle_prompt_gepa/events/`. Those archived counts are the evidence
used by prompt GEPA.

`tools/infra/aiclaw_chat.py` refuses common secret patterns by default:

- private key blocks
- OpenAI-style `sk-...` keys
- GitHub `gh*_...` tokens
- AWS `AKIA...` access keys
- simple `password=...`, `secret=...`, `token=...`, `api_key=...` assignments

Only use `--allow-sensitive` when the send is intentional and reviewed.

## DOM Generation State

The ChatGPT adapter identifies these page-level selectors:

```text
#prompt-textarea
[data-testid="send-button"]
[data-testid="stop-button"]
#composer-submit-button
[data-message-author-role="assistant"]
```

The generation-state logic in `chatgpt-adapter.ts` is:

- `stop-button` exists: generation is active.
- `send-button` exists: composer is idle and generation is considered complete.
- `stop-button` disappeared after generation started: generation is considered
  complete even if the submit button returns to a voice/blank composer state.
- assistant messages are read from `[data-message-author-role="assistant"]`
  first, with fallback selectors for DOM drift.

Important detail: ChatGPT may virtualize old messages. A visible assistant
message can temporarily read as `...` or empty text until scrolled into view.
The adapter scrolls the last assistant message into view and retries extraction.

## Read-Only DevTools Recovery

Use this only after a prompt has already been sent and the aiClaw API returned
an intermediate/suspect payload. This is a readback path, not a send path.

Check DevTools:

```bash
curl -sS http://127.0.0.1:9222/json/version
curl -sS http://127.0.0.1:9222/json
```

Locate the ChatGPT target:

```json
{
  "title": "ChatGPT",
  "type": "page",
  "url": "https://chatgpt.com/?temporary-chat=true",
  "webSocketDebuggerUrl": "ws://127.0.0.1:9222/devtools/page/..."
}
```

Read visible assistant messages through `browser-harness`:

```bash
browser-harness -c '
tab = [t for t in list_tabs() if "chatgpt.com" in t.get("url", "")][0]
switch_tab(tab)
expr = r"""
(() => {
  const selectors = [
    `[data-message-author-role="assistant"]`,
    `[class*="agent-turn"]`,
    `[class*="result-streaming"]`,
    `article[data-testid*="conversation-turn"]`
  ];
  const out = {
    title: document.title,
    url: location.href,
    stop: !!document.querySelector(`[data-testid="stop-button"]`),
    send: !!document.querySelector(`[data-testid="send-button"]`),
    selector: null,
    messages: []
  };
  for (const selector of selectors) {
    const nodes = Array.from(document.querySelectorAll(selector));
    if (nodes.length) {
      out.selector = selector;
      out.messages = nodes.map((n, i) => ({
        index: i,
        text: (n.innerText || n.textContent || ``).trim().slice(0, 4000)
      }));
      break;
    }
  }
  return out;
})()
"""
print(json.dumps(js(expr), indent=2))
'
```

Interpretation:

- `stop: true`: generation is still active. Wait; do not send another prompt.
- `stop: false` and `send: true`: page is idle; last assistant message is the
  best available final visible answer.
- `messages[-1].text == "Thinking"`: still suspect; wait and read again.
- `messages[-1].text` nonempty and not a known placeholder: record this as
  visible assistant output.

`switch_tab` activates the target and marks the title. It does not type, click,
or post. Avoid `goto_url`, `type_text`, `fill_input`, `click_at_xy`, and
`press_key` during readback unless the task explicitly requires browser
interaction.

## Event Trace Template

Use this template instead of claiming hidden reasoning recovery:

```text
aiClaw review event:
- preflight status:
  - platform: chatgpt
  - hasTab: true
  - isLoggedIn: true
  - active URL: https://chatgpt.com/?temporary-chat=true
- send:
  - command: python3 tools/infra/aiclaw_chat.py ask --wait --new --json ...
  - prompt hash: <sha256>
  - prompt chars: <count>
  - sent once: yes
- aiClaw response:
  - success: true
  - content: Thinking
  - conversation_id: null
  - raw.taskId: task_api_...
  - durationMs: ...
- task endpoint check:
  - /api/v1/tasks/<taskId>: NOT_FOUND
- readback:
  - method: browser-harness DevTools DOM read
  - stop-button: false
  - send-button: true
  - selector: [data-message-author-role="assistant"]
  - final visible message index: <n>
  - final visible message hash: <sha256>
- result:
  - final visible assistant text recorded
  - no second prompt sent
```

## SymPy Witness And Lean Verification Lane

The recovered archive witness lane is separate from ChatGPT review:

```bash
python3 tools/infra/auto_sympy_witnesses.py --run --strict
python3 tools/infra/auto_proof_pipeline.py
```

Current output shape:

```json
{
  "total_sympy_entries": 11,
  "runnable": 10,
  "repaired": 4,
  "passed": 10,
  "failed": 0,
  "skipped": 1
}
```

Generated witness files:

```text
witnesses/auto_sympy/original/
witnesses/auto_sympy/strict/
```

Generated reports:

```text
artifacts/auto_sympy/resurrected_witnesses.json
artifacts/auto_sympy/pipeline_report.json
```

Pipeline status fields:

- `witness_failed`: strict SymPy witness failure flag.
- `lean_failed`: Lean compile failure flag.
- `lean_checked`: number of Lean proof files checked.
- `vacuity_checked`: number of files scanned by vacuity audit.

If SymPy passes but Lean fails, the theorem is not closed. SymPy is diagnostic
evidence only.

## Arango Brain Separation

The aiClaw proof-memory Arango target defaults to:

```text
http://127.0.0.1:8540 / aiclaw_auto_rag
```

Configuration:

```bash
source configs/local/aiclaw_auto_arango.env.example
python3 tools/infra/aiclaw_auto_arango.py --dry-run init
python3 tools/infra/aiclaw_auto_arango.py --dry-run ingest
```

The wrapper refuses shared repo-DAG brain endpoints and databases unless
explicitly overridden:

```text
localhost:8530
127.0.0.1:8530
::1:8530
infogeometry
hive_live
```

Do not use `--allow-shared-brain` for proof-review memory. The default theorem
DAG Arango layer is for repo graph navigation and audit overlays, not aiClaw
dialog memory.

## Official OpenAI Distinction

This workflow drives the ChatGPT web UI through a local browser extension and
localBridge. It is not the official OpenAI API.

For API-native state, OpenAI documents Responses/Conversations and
`previous_response_id` as the state mechanisms:

- https://platform.openai.com/docs/guides/conversation-state
- https://platform.openai.com/docs/api-reference/responses

For ChatGPT Temporary Chat behavior:

- https://help.openai.com/en/articles/8914046-temporary-chat-faq

Those official API/state mechanisms do not expose private chain-of-thought
either. Use explicit visible messages, response IDs, tool outputs, and local
event logs as the audit chain.

## Failure Modes

`/api/v1/ai/status` says ready, but `/message` returns `Thinking`:

- Do not resend.
- Read the DOM final state.
- Record the `Thinking` payload as an intermediate extraction result.

`/api/v1/tasks/{taskId}` returns `NOT_FOUND`:

- Do not keep polling generic task API.
- The AI send path is not backed by the generic upload task store in this
  observed aiClaw build.

`stop-button` stays true:

- Generation is still active or stuck.
- Wait until timeout.
- If timeout expires, record timeout and do not send another prompt unless the
  user explicitly decides to retry.

Assistant text is `...` or empty:

- The page may have virtualized message content.
- Scroll the last assistant message into view and retry readback.

No ChatGPT target in DevTools:

- aiClaw may still see a tab through extension state, but DevTools is not
  exposing it.
- Use `python3 tools/infra/aiclaw_chat.py status`.
- Do not attempt blind navigation unless requested.

## Minimal Safe Review Loop

```bash
python3 tools/infra/aiclaw_chat.py wait --wait-timeout 30 --interval 1 --quiet
python3 tools/infra/aiclaw_chat.py ask --dry-run --prompt "$PROMPT"
python3 tools/infra/aiclaw_chat.py ask --wait --new --json --prompt "$PROMPT"
```

If final content is suspect:

```bash
curl -sS http://127.0.0.1:9222/json
browser-harness -c '<read-only DOM extraction script>'
```

Then record:

- the visible final assistant answer
- the command output and prompt hash/size
- the no-second-prompt fact
- any local build/proof verification that was run afterwards
