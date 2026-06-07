# Canonical Agent Pipeline

> Status: `authoritative quickstart`
> Scope: repository location, tool routing, aiClaw/ChatGPT lane discipline,
> Lean proof authority, graph tooling, Pi extensions, and GEPA prompt evolution.
> Rule: if another generated note conflicts with this file, this file wins.

## Repository

The canonical working tree is:

```bash
cd /home/goutev/repos/info-geometry-lean
```

Do not use `/home/goutev/auto`.

Do not infer another workspace from stale notes, generated examples, generated
transcripts, or external submodules. If an agent starts elsewhere, it must
return here before touching repo-owned code.

## Authority Stack

1. Lean source in the owner file.
2. `lake env lean <file>` or the locked Lake build.
3. Repo docs and skills.
4. Arango, DAG, RAG, SymPy, LeanTrail, Hodge, WL, de Bruijn, and ChatGPT as
   evidence only.

ChatGPT does not prove anything. It audits and suggests. The coding agent edits.
Lean decides.

## First Files To Read

For every agent session:

```text
AGENTS.md
docs/CANONICAL_AGENT_PIPELINE.md
docs/HIVE_AGENT_COMMANDMENTS.md
docs/REPO_DEEP_SEARCH_PROTOCOL.md
```

For categorical/tower/colimit work, also read:

```text
docs/CATEGORICAL_INFRASTRUCTURE_MAP.md
```

For Souriau-Bost-Connes capstone or crystallization claims, also read:

```text
docs/SOURIAU_BOST_CONNES_TRANSITION_STATUS.md
```

For detailed ChatGPT/aiClaw operation, also read:

```text
docs/AICLAW_CHATGPT_REVIEW_RUNBOOK.md
```

## Correct Tool Routing

### Lean Verification

Use a narrow file check while editing:

```bash
lake env lean lean/InfoGeometry/Path/To/File.lean
```

Use the locked build wrapper for module builds:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Path.To.Module
```

### Context Preflight

Before answering nontrivial repository-content questions, build a bounded
context packet instead of relying on stale docs or filenames:

```bash
python3 tools/infra/context_preflight.py "question or target theorem" --include-external
```

This packet separates repo-owned code, external references, graph/indexing
surfaces, Lean owner candidates, and generated artifact presence. It is
navigation evidence only; proof claims still require Lean owner validation.

### aiClaw / ChatGPT Oracle

The ChatGPT browser lane is single-flight per platform. Always check it before
sending:

```bash
python3 tools/infra/aiclaw_chat.py status
python3 tools/infra/aiclaw_chat.py queue-status --platform chatgpt
```

For proof repair, dry-run first:

```bash
python3 tools/infra/socratic_clawbot.py \
  --file lean/InfoGeometry/Path/To/File.lean \
  --theorem theorem_name \
  --dry-run --json
```

Then send one prompt, with complete owner file and full relevant build output:

```bash
python3 tools/infra/socratic_clawbot.py \
  --file lean/InfoGeometry/Path/To/File.lean \
  --theorem theorem_name \
  --response-out artifacts/oracle/theorem_name.md \
  --json-out artifacts/oracle/theorem_name.json
```

If aiClaw returns `Thinking`, times out after a possible send, or leaves the
browser tab mid-generation, do not send another prompt. Recover the final
visible browser answer read-only, record it, then release:

```bash
python3 tools/infra/aiclaw_chat.py queue-release \
  --platform chatgpt \
  --reason final_visible_answer_recorded
```

### Pi Extension Stack

Use:

```bash
./run.sh "Use local Lean checks first. If blocked, call ask_chatgpt_compiler with the owner file and exact build error."
```

Minimal Pi invocation:

```bash
pi --model deepseek/deepseek-v4-flash \
  -e ./chatgpt-oracle.ts \
  -e ./lean-prover-tool.ts \
  "Run a narrow Lean proof repair. Use ask_chatgpt_compiler only after local debugging stalls."
```

`chatgpt-oracle.ts` must route through `tools/infra/aiclaw_chat.py` first and
only then fall back to an OpenAI-compatible API.

`agent-orchestrator.ts` is an interactive Pi tool surface. It is not merely a
prompt template: `queue_run_next` must execute the concrete local worker
sequence and archive a report. Its queue contract is:

```text
task_queue.json
proofs/<task-id>.lean
proofs/<task-id>.sp
artifacts/agent_orchestrator/*.json
```

The required execution sequence is:

```text
Researcher + Algebraist(SymPy) in parallel
then Formalist(Lean)
then Critic(vacuity linter)
then Archivist(report artifact)
```

SymPy witnesses are persistent source artifacts. Do not use fixed temp files
such as `.temp_witness.py`; store the witness side-by-side with the Lean file as
`proofs/<task-id>.sp`.

### Archon Definite Sequences

Archon owns repeatable, deterministic DAG/loop execution. The Archon repo
describes workflows as YAML with deterministic bash/script nodes plus AI nodes,
so this repo routes long-running theorem queue execution through:

```bash
python3 tools/infra/agent_orchestrator_queue.py status
python3 tools/infra/agent_orchestrator_queue.py run-next
```

The matching workflow is:

```text
.archon/workflows/agent-orchestrator-definite-sequence.yaml
```

Run it from this repository root with the repo wrapper:

```bash
./scripts/run_agent_orchestrator_archon.sh
```

The wrapper sets:

```text
ARCHON_HOME=/home/goutev/repos/info-geometry-lean/.runtime/archon-home
```

If you call Archon manually, set `ARCHON_HOME` yourself before invoking the CLI:

```bash
cd tools/archon
ARCHON_HOME=/home/goutev/repos/info-geometry-lean/.runtime/archon-home \
  bun run cli workflow run agent-orchestrator-definite-sequence --cwd /home/goutev/repos/info-geometry-lean
```

Do not create a second theorem queue for Archon. Archon calls the Python bridge;
Pi calls the TypeScript extension; both use the same queue files and artifacts.

`run.sh` also defaults runtime state to:

```text
INFO_GEOMETRY_RUNTIME_DIR=/home/goutev/repos/info-geometry-lean/.runtime
PI_RUNTIME_HOME=/home/goutev/repos/info-geometry-lean/.runtime/pi-home
ARCHON_HOME=/home/goutev/repos/info-geometry-lean/.runtime/archon-home
```

The final Pi command is launched with `HOME="$PI_RUNTIME_HOME"` so Pi writes
`.pi` state under `.runtime/pi-home/.pi` rather than `/home/goutev/.pi`.

### GEPA Prompt Evolution

GEPA is archive-first. It scores recorded outcomes and prompt profiles; it does
not replace the stable oracle prompt just because a generated note says so.

```bash
npm run ai:oracle:gepa
npm run ai:oracle:gepa:gate
```

Record proof-repair outcomes before trusting prompt mutations:

```bash
npm run ai:oracle:record -- --event-json artifacts/oracle/target_theorem_name.json
```

### GEPA Review Mode For Archon SOPs

GEPA may optimize Archon SOPs only in review mode. The intended loop is:

```text
Archon workflow run
  -> observed task outcomes, timings, failures, vacuity findings, build verdicts
  -> thermodynamic scoring / statistical variability analysis
  -> GEPA proposes candidate SOP mutation
  -> candidate is written to quarantine/review, not to .archon/workflows
  -> human or explicit promotion gate reviews the candidate
  -> only accepted candidates become maintained SOP/workflow source
```

The reason is operational, not cosmetic: agents introduce statistical
variability even when they are told to follow an SOP. GEPA is useful because it
can observe that variability empirically and propose better instructions. It is
not authority to replace the stable Archon reflex by itself.

Hard boundaries:

- GEPA output is a proposal until reviewed.
- `.archon/workflows/*.yaml` remains stable reflex source.
- `quarantine/hermes_skills/`, `artifacts/`, and reports are evidence, not
  promoted commandment text.
- Promotion requires the same evidence as any other workflow change: source diff,
  rollback path, representative run artifact, policy/vacuity result, and Lean or
  Lake verdict for touched proof surfaces.
- If a mutation only improves prose but does not improve measured execution, it
  stays archived.

### GEPA Agent Message Observer

The default observer watches communication payloads, not SOP text. It records
what agents submit to model/oracle/collaborator lanes and what those lanes
return. This includes aiClaw/ChatGPT, Pi/DeepSeek, Hermes, Gemini CLI, Google AI
browser lanes, and OpenAI-compatible advisory calls when the maintained sender
script is instrumented.

Append-only redacted ledger:

```bash
python3 tools/infra/agent_message_ledger.py \
  --source-tool manual \
  --channel manual_external_oracle \
  --prompt-file /tmp/prompt.txt \
  --response-file /tmp/response.txt
```

GEPA review packet from observed traffic:

```bash
python3 tools/infra/gepa_agent_message_observer.py --json
```

Outputs:

```text
artifacts/agent_messages/YYYYMMDD_agent_messages.jsonl
artifacts/gepa_agent_message_observer/*_message_observations.jsonl
artifacts/gepa_agent_message_observer/*_message_report.json
quarantine/agent_message_reviews/*_message_review.md
```

The ledger stores redacted text excerpts plus full prompt/response hashes. It
is empirical evidence for prompt/process improvement. It is not proof authority
and it must not silently mutate Archon workflows, commandments, skills, or Lean
source.

### Graph / DAG / Arango

Graph tools identify candidate wires only. They do not prove theorem content.

For DAG/Arango/LeanTrail/Hodge/de Bruijn/WL cleanup tasks, use:

```text
skills/lean-dag-wire-refactor/SKILL.md
```

Keep aiClaw proof memory separate from the repo theorem-DAG Arango brain.

## Forbidden Routes

Do not use these for repo-owned ChatGPT work:

- direct `ws://localhost:1956` WebSocket bridge;
- raw browser-harness DOM prompt injection without
  `tools/infra/chatgpt_lane_guard.py`;
- manual Enter-key fallback when the ChatGPT send button is disabled;
- stacked prompts while a prior answer may still be generating;
- archived generated transcripts as implementation sources;
- ChatGPT full-file replacement without a subsequent Lean check;
- SymPy/RAG/graph evidence as proof authority;
- generated wrappers, `axiom`, `sorry`, `admit`, `unsafe`, or `: True`
  theorem surfaces to hide proof debt.

## Minimal Correct Proof-Repair Loop

```text
1. cd /home/goutev/repos/info-geometry-lean
2. Read AGENTS.md and this file.
3. Locate the Lean owner file and owner theorem.
4. Run lake env lean on the owner file.
5. If local repair is possible, edit only the owner surface and recheck.
6. If blocked, run socratic_clawbot.py --dry-run --json.
7. Check aiClaw status and queue-status.
8. Send one complete owner-file oracle prompt through socratic_clawbot.py.
9. If the lane is suspect, recover read-only final browser output before release.
10. Apply only source changes the coding agent understands.
11. Re-run lake env lean or the locked Lake build.
12. Record oracle outcome if GEPA will use it.
```

This is the pipeline future agents should follow. Long generated transcripts
are historical context, not routing authority.
