# Hive Beehive Migration Plan (surgical, no rewrite)

> Status: `reference memory`
> Audited: 2026-05-16
> Scope: migrate the current Hive notes and runtime toward the optimal beehive architecture
> Source docs read: `docs/hive_greenfield_architecture.md`, `docs/hive_graph_resident_os.md`, `docs/hermes_recursive_hive_architecture.md`, `docs/hive_neural_backbone_architecture.md`, `docs/hive_beehive_swarm_implementation_plan.md`
> Authority: planning only; Lean, Lake, audit, and promotion gates remain authoritative.

## 0. Goal

Move the repo from a mix of historical swarm notes into one coherent, local-first, Lean-authoritative beehive architecture.

The migration should preserve what already works and only change the parts that are currently ambiguous:

- control-plane state
- packet typing
- provider routing
- worker boundaries
- runtime observability
- document hierarchy

## 1. Current baseline

Already present in the repo:

- Arango-backed queue/runtime substrate in `tools/infra/hive_arango_queue.py`
- Worker flow in `tools/infra/hive_bee.py`
- Swarm orchestration in `tools/infra/hive_swarm.py`
- Build worker in `tools/infra/hive_build_worker.py`
- Audit worker in `tools/infra/hive_audit_worker.py`
- Research digestion worker in `tools/infra/research_digest_worker.py`
- Locked build wrapper in `tools/infra/run_locked_lake_build.py`
- Hive packet schemas in `tools/schema/hive/*.schema.json`
- Runtime control schemas in `tools/schema/hive_runtime/*.schema.json`

The migration is therefore a hardening and consolidation pass, not a rewrite.

## 2. Target architecture

Target layers:

1. Control plane
2. Cognition plane
3. Execution plane
4. Storage plane
5. Cockpit plane

Target principle:
- every task has a narrow owner
- every transition emits a packet/event
- every long-running job has explicit state
- every verification result is separated from promotion
- every provider fallback is live-tested before being trusted

## 3. Phase plan

### Phase 1: declare the canonical architecture

Objective:
- make the architecture explicit in docs before changing runtime behavior.

Files:
- modify: `docs/hive_greenfield_architecture.md`
- modify: `docs/hive_migration_plan.md`
- optionally update: `docs/README.md` links if the docs index needs a canonical pointer

Deliverable:
- one architecture doc and one migration doc that describe the same target topology.

### Phase 2: normalize runtime packet vocabulary

Objective:
- make the task and gate vocabulary consistent across workers and docs.

Current surface to align:
- `GoalPacket`
- `AttemptPacket`
- `GateReport`
- `ExecutionIntentPacket`
- `LeanVerificationPacket`
- `BuildPacket`
- `AuditPacket`
- `PromotionDecisionPacket`

Files:
- inspect: `tools/schema/hive_runtime/*.schema.json`
- inspect: `tools/schema/hive/*.schema.json`
- inspect: worker code in `tools/infra/hive_*.py`

Acceptance:
- runtime terms are consistent across docs, schema, and worker outputs.

### Phase 3: keep provider routing explicit and verified

Objective:
- prevent swarm workers from depending on speculative or broken model routes.

Recommended verified chain in this environment:
- primary: `openrouter/free`
- fallback: `openai-codex gpt-5.4`
- lightweight fallback: `openai-codex gpt-5.4-mini`
- last resort: `gemini gemini-3-flash-preview`

Files:
- modify: `~/.hermes/config.yaml`
- inspect: `~/.hermes/.env`
- inspect: repo-local `.env` and `.archon/.env`

Acceptance:
- `hermes config check` passes
- `hermes fallback list` matches the intended chain
- each kept provider/model combination has a live chat success

### Phase 4: make control-plane state explicit

Objective:
- surface queue claims, lease waits, retries, and build waits as visible state instead of implied behavior.

Files to inspect and likely extend:
- `tools/infra/hive_arango_queue.py`
- `tools/infra/hive_bee.py`
- `tools/infra/hive_swarm.py`
- `tools/infra/run_locked_lake_build.py`

Desired states:
- queued
- claimed
- running
- lock_wait
- completed
- failed
- timed_out
- cancelled
- quarantined

Acceptance:
- operators can tell proof failure from queue wait from build lock wait.

### Phase 5: keep worker lanes narrow

Objective:
- ensure each worker remains a specialist rather than a monolith.

Recommended lanes:
- retrieval lane
- proposal lane
- critique lane
- Lean verification lane
- build lane
- audit lane
- promotion lane
- research lane
- telemetry lane

Files:
- inspect: `tools/infra/hive_bee.py`
- inspect: `tools/infra/hive_swarm.py`
- inspect: `tools/infra/research_digest_worker.py`
- inspect: `tools/infra/hive_build_worker.py`
- inspect: `tools/infra/hive_audit_worker.py`

Acceptance:
- lane responsibilities are distinct and documented.

### Phase 6: separate storage concerns

Objective:
- keep theorem DAG, Hive runtime state, and artifact storage separate.

Files:
- inspect current Arango config / DB handling
- keep theorem graph memory separate from task runtime collections
- keep filesystem artifacts as replayable evidence, not truth authority

Acceptance:
- no doc or worker conflates DAG memory with Hive execution state.

### Phase 7: add explicit observability and replay

Objective:
- ensure every meaningful action becomes replayable evidence.

Desired artifacts:
- event trails
- fossil/deadend records
- gate reports
- per-goal lineage summaries
- worker heartbeats

Acceptance:
- a task can be reconstructed from packet lineage alone.

## 4. What not to change yet

Do not:
- merge the Hive runtime database with the theorem DAG database
- collapse proof, build, audit, and promotion into one worker
- remove `run_locked_lake_build.py` before a resource-aware replacement exists
- treat semantic retrieval as truth authority
- keep undocumented fallback chains
- assume local fallback models are reliable without live verification
- assume Copilot auth works just because GitHub CLI auth works

## 5. Recommended smoke tests

After any architecture/routing change, run:

1. `hermes config check`
2. `hermes fallback list`
3. live chat verification for the kept primary/fallback providers
4. queue/runtime init for Hive-Arango tools
5. a synthetic task path that emits:
   - GoalPacket
   - AttemptPacket
   - GateReport
   - at least one verification or deadend record

## 6. Update sequence for the docs

If editing docs only, the safest sequence is:

1. Rewrite the architecture doc first.
2. Rewrite the migration plan second.
3. Re-read both docs for consistency.
4. Update the docs index only if the index needs a canonical pointer.

## 7. Success criterion

The migration is done when the beehive behaves like a real operating system for theorem work:

- Hermes coordinates
- workers stay narrow
- packets carry lineage
- Arango remembers
- Lean decides truth
- build/audit/promotion remain distinct
- and no one has to infer state from terminal chatter
