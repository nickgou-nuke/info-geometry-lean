# Hive Agent Commandments

> Status: `current authority`
> Scope: operational law for agents working in `info-geometry-lean`.
> Rule: if a transcript, archived note, or generated report conflicts with this
> file, this file wins.

## The Ten Commandments

1. **Work in the one true repository.**
   Always start from `/home/goutev/repos/info-geometry-lean`. Do not use stale
   paths such as `/home/goutev/auto`, generated handover paths, or external
   submodules as the working tree for repo-owned edits.

2. **Read the routing law before touching code.**
   Read `AGENTS.md`, `docs/CANONICAL_AGENT_PIPELINE.md`, and this file first.
   For categorical, colimit, tower, Fibonacci, Grothendieck, or tensor work,
   also read `docs/CATEGORICAL_INFRASTRUCTURE_MAP.md`.

3. **Lean owner files decide truth.**
   GraphRAG, Arango, LeanTrail, Hodge/WL/de Bruijn scans, SymPy, GEPA, Pi,
   Archon, and ChatGPT are navigation or suggestion layers only. A claim counts
   only after the owner Lean source compiles through `lake env lean <file>` or a
   targeted Lake build.

   Before answering repository-content questions, follow
   `docs/REPO_DEEP_SEARCH_PROTOCOL.md`. Search executable code surfaces, Lake
   scripts, Python/TypeScript entrypoints, graph ingesters, and Lean owners.
   Treat docs, docstrings, transcripts, and generated reports as hints until
   code or build output confirms them.

4. **Do not fake closure.**
   Never hide proof debt behind `axiom`, `admit`, `unsafe`, `: True`, vacuous
   theorem wrappers, renamed placeholders, or prose saying "verified" when the
   owner theorem is not proved. If debt remains, name it as closure debt.
   High-risk capstone narratives such as the Souriau-Bost-Connes transition
   lane must obey `docs/SOURIAU_BOST_CONNES_TRANSITION_STATUS.md`.

5. **Use the owner layer, not a duplicate bridge.**
   Do not rebuild categorical infrastructure. The categorical owners include
   `Algebra/Grothendieck.lean`, `Canonical/TensorTowerColimit.lean`, and
   `Categorical/FibonacciBraiding.lean`. Matrix-level files are readouts or
   instances, not replacements.

6. **Run the canonical pipeline, not improvised tools.**
   Use the maintained entry points:

   ```bash
   ./run.sh "Use local Lean checks first. If blocked, call ask_chatgpt_compiler with the owner file and exact build error."
   ./scripts/run_agent_orchestrator_archon.sh
   tools/infra/gepa_categorical_projection.py --evolve --generations 10
   ```

   GEPA may observe Archon runs, score empirical variability, and propose new
   SOPs. Those proposals belong in quarantine/review until a human or explicit
   promotion gate accepts them. GEPA must not silently rewrite stable Archon
   workflows or commandments.

   The agent-message observer watches generated prompt/response traffic, not
   SOP files. Instrumented model/oracle/collaborator lanes write redacted,
   hash-bearing events to `artifacts/agent_messages/`. Run:

   ```bash
   python3 tools/infra/gepa_agent_message_observer.py --json
   ```

   The output is review evidence in `quarantine/agent_message_reviews/`, not an
   automatic promotion into Archon workflows, skills, commandments, or Lean
   source.

   For Lean checks:

   ```bash
   lake env lean lean/InfoGeometry/Path/To/File.lean
   python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Path.To.Module
   ```

   Browser oracle lanes are single-flight state machines, not free-form chat
   tabs. Before using aiClaw, run:

   ```bash
   python3 tools/infra/aiclaw_chat.py queue-status --platform chatgpt
   ```

   Follow `queue_state` and `agent_action`. `ready` permits exactly one send.
   `active` means wait. `needs_readback` means recover the final visible answer
   with read-only browser inspection, record it, then run `queue-release`; it is
   not a hard provider block. `stale_active` with dead process markers can be
   archived with `queue-prune-active`. Do not stack prompts behind a held lane.
   Google AI Mode uses the browser-harness lane `scripts/google-ai-search.sh`;
   do not mix it with aiClaw Gemini or ChatGPT queues.

7. **Keep runtime state isolated.**
   Pi and Archon state live under repo-local `.runtime/`:

   ```text
   .runtime/pi-home/.pi
   .runtime/archon-home
   ```

   Do not depend on `/home/goutev/.pi` or `/home/goutev/.archon`. The Archon
   definite-sequence wrapper defaults to Pi with
   `deepseek/deepseek-v4-flash` and skips title generation so it does not fall
   back to `openai-codex`.

8. **Do not leak or guess credentials.**
   Presence checks are allowed; printing key values is not. The local DeepSeek
   key source is `.DEEPSEEK_API_KEY`, and the runtime wrapper loads it without
   exposing it. If Pi reports a provider-auth issue, inspect provider routing
   and env-var mapping before changing models.

9. **Preserve SymPy and Lean evidence side by side.**
   Researcher and Algebraist context may run before the Formalist, but SymPy
   witnesses are persistent artifacts, not temp scratch. Store them as
   `proofs/<task-id>.sp` next to `proofs/<task-id>.lean`. Do not use fixed temp
   names such as `.temp_witness.py`.

10. **Archive artifacts, commit sources.**
    Do not commit generated run debris from `artifacts/`, `reports/`,
    `.runtime/`, or scratch folders unless explicitly requested. Track source
    files, maintained docs, tests, scripts, and theorem-owner files. Do not edit
    dirty external submodules unless explicitly asked.

## Canonical Definite Sequence

The theorem-queue workflow is:

```text
Researcher + Algebraist(SymPy) in parallel
then Formalist(Lean)
then Critic(vacuity and theorem-honesty audit)
then Archivist(report artifact)
```

The queue contract is:

```text
task_queue.json
proofs/<task-id>.lean
proofs/<task-id>.sp
artifacts/agent_orchestrator/*.json
```

The maintained command is:

```bash
./scripts/run_agent_orchestrator_archon.sh
```

Successful provider resolution must look like:

```text
provider: pi
model: deepseek/deepseek-v4-flash
ARCHON_HOME=/home/goutev/repos/info-geometry-lean/.runtime/archon-home
```

If a run reports `openai-codex` auth during this pipeline, that is a routing
bug, not a proof failure. Check `scripts/run_agent_orchestrator_archon.sh`,
`.archon/workflows/agent-orchestrator-definite-sequence.yaml`, and the local
Archon Pi provider mapping before retrying.

## Minimal Session Checklist

```text
1. cd /home/goutev/repos/info-geometry-lean
2. Read AGENTS.md, docs/CANONICAL_AGENT_PIPELINE.md, docs/HIVE_AGENT_COMMANDMENTS.md.
   For repository-content questions, also read docs/REPO_DEEP_SEARCH_PROTOCOL.md.
3. Identify the owner Lean module or maintained script.
4. Inspect current git status and do not revert unrelated changes.
5. Make the smallest source edit with apply_patch.
6. Run the narrow validation command.
7. Scan touched files for fake closure markers.
8. If using ChatGPT, use the aiClaw single-flight lane only and obey
   `queue_state`.
9. Put SymPy witnesses beside Lean witnesses.
10. Report exact changed files and validation evidence.
```
