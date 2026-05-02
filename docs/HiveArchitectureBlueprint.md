# Hive Architecture Blueprint (Code-Grounded, April 2026)

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

> Scope: blueprint derived from current repo implementation (`tools/infra/*`, `lean/InfoGeometry/Meta/HiveLogos.lean`, and `tests/test_hive_*`).
> Purpose: stabilize the trust boundary and provide an executable architecture plan for the current Hive stack.

## 1) Architectural invariant (non-negotiable)

Truth boundary:
- LLM workers may propose tactics.
- Only Lean kernel verification can promote outputs to fossil memory.
- Everything else is retrieval/proposal/audit metadata.

Code anchors:
- `lean/InfoGeometry/Meta/HiveLogos.lean`
- `tools/infra/hive_bee.py`
- `tools/infra/hive_swarm.py`
- `tools/infra/hive_arango_queue.py`

## 2) Current implemented system (as-is)

### 2.1 Planes

1. Logos plane (formal)
- Lean command/tactic emitters:
  - `hive_probe` emits `InfoTreeArtifact` as `HIVE_JSON ...`
  - `#hive_index_decl` emits `DiamondFossil` as `HIVE_JSON ...`
- Canonical shape extraction:
  - instantiate mvars -> whnf -> abstract used fvars -> shape string.

2. Ingestion/event plane
- `tools/infra/ingest_hive_json.py` parses `HIVE_JSON` lines and normalizes to `info_geometry.hive_memory.v1` records.
- Stable hashes:
  - `packet_sha256` over canonical JSON packet.
  - `shape_sha256` over canonical shape string.

3. Queue/control plane (MotherBee substrate)
- `tools/infra/hive_arango_queue.py`
- Responsibilities:
  - schema/bootstrap ArangoDB
  - task leasing/requeue/fail/complete
  - worker heartbeat
  - status updates and queue stats

4. Retrieval/proposal/execution plane
- `tools/infra/hive_bee.py` (single-bee flow)
- `tools/infra/hive_swarm.py` (generator+critic+auditor orchestration)
- Retrieval source:
  - `tools/infra/arango_gravity_context.py` (faithful raw graph preferred)
- Proposal:
  - OpenAI-compatible prover call via `hermes_bounded_runner.call_openai_compatible`
- Verification:
  - Lean REPL bridge (`lean_interact_wrapper.apply_tactic/get_proof_state`)

5. Recirculation/audit plane
- Dead-end capture: `hive_deadends`
- Replay packet capture: `hive_replay_packets`
- Swarm run artifacts: `artifacts/hermes_loop/hive_swarm/*.json`

### 2.2 ArangoDB logical model

Document collections:
- `hive_goals`
- `hive_fossils`
- `hive_deadends`
- `hive_replay_packets`
- `hive_tasks`
- `hive_workers`
- `hive_events`

Edge collections:
- `hive_goal_closed_by`
- `hive_goal_rejected_by`
- `hive_task_for_goal`
- `hive_event_about`

Key indexes (selection):
- `hive_tasks(queue_name,status,priority)` for dispatch ordering
- `hive_tasks(lease_expires_at)` for lease recovery
- `hive_goals(goal_hash_shape)`
- `hive_fossils(conclusion_hash_shape)`
- `hive_events(packet_sha256)` unique dedup

### 2.3 Queue state machine (implemented)

Task states:
- `pending -> leased -> completed`
- `leased -> pending` (requeue)
- `leased -> failed`
- `pending|expired leased -> leased` via claim renewal pattern

Goal states (used by bees/swarm):
- `open -> retrieved -> generated -> criticized -> checked -> audited`
- Failure branches: `requeued` or `deadend`

## 3) End-to-end executable flows

### 3.1 Seed flow
1. Lean emits HIVE_JSON packets.
2. `ingest_hive_json.py` creates normalized JSONL.
3. `hive_arango_queue.py seed` routes:
   - `InfoTreeArtifact` -> goals + tasks
   - `DiamondFossil/TheoremFossil` -> fossils
   - all packets -> events + event edges

### 3.2 Single-bee proof flow
1. Claim next task (`claim_next_task`).
2. Load goal and run gravitational retrieval context.
3. Generate tactic from model.
4. Apply tactic through Lean.
5. If success:
   - generated theorem check + `#hive_index_decl`
   - ingest fossil records
   - write replay packet
   - complete task + close/audit goal
6. If failure:
   - record deadend
   - requeue until attempt cap, then fail/deadend

### 3.3 Swarm proof flow
1. Generator proposes tactic.
2. Critic approves/revises/rejects.
3. Formalizer stage executes Lean verification.
4. Auditor emits trust-boundary report.
5. Persist swarm run artifact + queue/goal updates.

## 4) Architecture gaps (current)

1. Policy and schema drift risk
- State labels and packet semantics are spread across scripts/tests without one canonical contract file.

2. Separation of concerns
- Some worker modules contain orchestration + persistence + replay construction in one file (`hive_bee.py`), increasing coupling.

3. Replay verifiability
- Replay packets are rich, but no dedicated replay verifier CLI currently enforces deterministic re-check in CI.

4. Queue fairness and prioritization strategy
- Current queue sorting uses priority then creation time; no explicit aging/anti-starvation policy.

5. Auth/runtime hardening
- Local defaults are convenient for dev; production profile model (secrets/roles/ACL) is not codified as a deployment profile doc.

## 5) Target blueprint (to build now)

### 5.1 Service decomposition

A. `hive-kernel-adapter` (Lean side)
- Own only HIVE_JSON emission and canonicalization policy.
- Export explicit versioned packet contract (`v1`, then `v2`).

B. `hive-ingest-gateway`
- Own ingest validation, schema checks, and dedup behavior.
- Reject malformed/partial packets before queue insertion.

C. `motherbee-queue`
- Own leasing, retries, worker heartbeats, and SLAs.
- Provide queue policy plugin: `priority + age + retry_penalty`.

D. `bee-workers`
- `bee-generator`, `bee-critic`, `bee-formalizer`, `bee-auditor` as role workers.
- Keep each worker stateless; persist all side effects through queue/gateway APIs.

E. `hive-replay-verifier`
- Deterministically re-run replay packets.
- Emit pass/fail attestations and delta diagnostics.

### 5.2 Contracts to freeze

1. Packet contract:
- `info_geometry.hive_memory.v1` (current)
- Add explicit required/optional field registry in one markdown contract doc.

2. Queue contract:
- Allowed task statuses and transitions.
- Allowed goal statuses and transitions.
- Retry cap semantics and deadend promotion rule.

3. Trust-boundary contract:
- Fossil promotion requires Lean success + index emission.
- Auditor is advisory; cannot override kernel result.

### 5.3 Observability blueprint

Minimum telemetry per run:
- queue wait time
- lease duration used
- retrieval latency
- model latency
- lean verification latency
- recirculation count
- fossilization rate

Store these in `hive_events` with typed event payloads (`hive.metric.*`).

## 6) Implementation plan (small, executable slices)

Slice 1: Contract surfaces
- Add `docs/HivePacketContract.md` and `docs/HiveQueueContract.md`.
- Encode status transition table and required fields.

Slice 2: Replay verifier
- Add `tools/infra/hive_replay_verify.py`:
  - load replay packet
  - regenerate theorem file
  - run Lean check
  - compare expected vs actual fossil hashes

Slice 3: Queue fairness policy
- Extend `claim_next_task` AQL with optional aging coefficient.
- Add policy args to CLI and tests.

Slice 4: Worker decomposition
- Split `hive_bee.py` into:
  - retrieval module
  - tactic proposal module
  - fossilization/replay module
  - orchestration entrypoint

Slice 5: CI lane
- Add a lightweight Hive integration test lane (mock Arango + fixture packets + replay verification).

## 7) Verification checklist for this blueprint

- [ ] `hive_probe` and `#hive_index_decl` packet format documented and versioned
- [ ] queue/goal state transitions documented and tested
- [ ] replay verifier passes on known-good fossil fixture
- [ ] deadend/requeue policy deterministic under repeated failures
- [ ] telemetry emitted for each worker run phase

## 8) Immediate next command set (operator runbook)

1. Validate queue schema status
- `python3 tools/infra/hive_arango_queue.py status --endpoint http://127.0.0.1:8530 --database hive_live`

2. Run single swarm tick
- `python3 tools/infra/hive_swarm.py --once`

3. Run single bee tick
- `python3 tools/infra/hive_bee.py --once`

4. Inspect artifacts
- `artifacts/hermes_loop/hive_swarm/`
- `artifacts/hermes_loop/hive_bee/`
- `artifacts/hermes_loop/hive_memory/`

---

This blueprint keeps the current repo’s core doctrine intact: exploratory intelligence can be broad, but memory promotion remains kernel-gated.
