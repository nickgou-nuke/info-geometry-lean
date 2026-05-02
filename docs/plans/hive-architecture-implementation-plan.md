# Hive Architecture Hardening Implementation Plan

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../../README.md), [docs/README.md](../README.md), [docs/CODEBASE_STATUS.md](../CODEBASE_STATUS.md)

> For Hermes: Use subagent-driven-development skill to implement this plan task-by-task.

Goal: Hardening the current Hive stack into a contract-first, replay-verifiable architecture while preserving the Lean-kernel trust boundary.

Architecture: Keep existing modules (`hive_bee`, `hive_swarm`, `hive_arango_queue`, `ingest_hive_json`, `HiveLogos.lean`) but add explicit contracts, deterministic replay verification, queue fairness policy, and better module boundaries. Implement in thin vertical slices so every slice is testable in isolation.

Tech stack: Lean 4, Python 3, ArangoDB AQL, pytest via `scripts/run_tests.sh`, JSONL packet surfaces.

---

## Task 1: Create packet contract doc

Objective: Freeze current `info_geometry.hive_memory.v1` packet contract in one authoritative markdown surface.

Files:
- Create: `docs/HivePacketContract.md`
- Reference: `tools/infra/ingest_hive_json.py`, `lean/InfoGeometry/Meta/HiveLogos.lean`

Step 1: Write required fields section
- Required: `schema`, `artifact_kind`, `space`, `entity_key`, `canonical_shape`, `packet_sha256`, `shape_sha256`, `packet`.
- Include type constraints and nullability.

Step 2: Write artifact-specific sections
- `InfoTreeArtifact` fields expected from `hive_probe`.
- `DiamondFossil` fields expected from `#hive_index_decl`.

Step 3: Add canonicalization policy section
- Declare current policy: instantiate mvars -> whnf -> abstract used fvars -> shape string.

Step 4: Add malformed packet handling policy
- Define reject/skip behavior and required error messages.

Step 5: Commit
- `git add docs/HivePacketContract.md`
- `git commit -m "docs: add hive packet contract v1"`

## Task 2: Create queue contract doc

Objective: Freeze queue/task/goal transitions and operational semantics.

Files:
- Create: `docs/HiveQueueContract.md`
- Reference: `tools/infra/hive_arango_queue.py`, `tools/infra/hive_bee.py`, `tools/infra/hive_swarm.py`

Step 1: Document task states and transitions
- `pending -> leased -> completed`
- `leased -> pending` (requeue)
- `leased -> failed`

Step 2: Document goal states and transitions
- `open -> retrieved -> generated -> criticized -> checked -> audited`
- failure branches to `requeued` and `deadend`.

Step 3: Document lease and retry semantics
- lease expiration behavior
- `claim_count` semantics
- max-attempt deadend rule.

Step 4: Add AQL truth table appendix
- Short table mapping state transitions to functions.

Step 5: Commit
- `git add docs/HiveQueueContract.md`
- `git commit -m "docs: add hive queue contract and state transitions"`

## Task 3: Link new contract docs in doc indexes

Objective: Make contracts discoverable through current docs map.

Files:
- Modify: `docs/README.md`
- Modify: `docs/RepositoryMemoryMap.md`

Step 1: Add links under maintained/current surfaces.
Step 2: Verify links render and path is correct.
Step 3: Commit
- `git add docs/README.md docs/RepositoryMemoryMap.md`
- `git commit -m "docs: index hive contract surfaces"`

## Task 4: Add packet validation helper module

Objective: Centralize packet validation rules currently implicit in ingestion and workers.

Files:
- Create: `tools/infra/hive_packet_contract.py`
- Modify: `tools/infra/ingest_hive_json.py`

Step 1: Implement validator API
- `validate_record(record: dict) -> tuple[bool, list[str]]`
- `validate_packet(packet: dict) -> tuple[bool, list[str]]`

Step 2: Wire ingestion to validator
- On invalid packet: raise `HiveIngestError` with field-specific message.

Step 3: Add lightweight unit tests
- Create: `tests/test_hive_packet_contract.py`

Step 4: Run tests
- `scripts/run_tests.sh tests/test_hive_packet_contract.py -v`
- Expected: all tests pass.

Step 5: Commit
- `git add tools/infra/hive_packet_contract.py tools/infra/ingest_hive_json.py tests/test_hive_packet_contract.py`
- `git commit -m "feat: add hive packet validator and ingestion checks"`

## Task 5: Add queue transition guard helper

Objective: Prevent accidental illegal status updates from worker code.

Files:
- Create: `tools/infra/hive_queue_contract.py`
- Modify: `tools/infra/hive_arango_queue.py`

Step 1: Encode allowed transitions map
- `allowed_task_transition(old, new)`
- `allowed_goal_transition(old, new)`

Step 2: Add optional guard flag in update functions
- Validate transitions before AQL update.

Step 3: Add tests
- Create: `tests/test_hive_queue_contract.py`

Step 4: Run tests
- `scripts/run_tests.sh tests/test_hive_queue_contract.py tests/test_hive_arango_queue.py -v`
- Expected: pass, existing behavior preserved for valid transitions.

Step 5: Commit
- `git add tools/infra/hive_queue_contract.py tools/infra/hive_arango_queue.py tests/test_hive_queue_contract.py`
- `git commit -m "feat: add queue transition guards for hive state machine"`

## Task 6: Build replay verifier CLI (core)

Objective: Deterministically re-check replay packets against Lean and compare outcome hashes.

Files:
- Create: `tools/infra/hive_replay_verify.py`
- Reference: `tools/infra/hive_bee.py`, `tools/infra/ingest_hive_json.py`

Step 1: Implement CLI inputs
- `--replay-packet <json path>`
- `--timeout <seconds>`
- `--strict` (fail on any mismatch)

Step 2: Implement replay execution
- materialize theorem source from replay packet
- run `lake env lean <tempfile>`
- re-ingest output with `ingest_text`

Step 3: Implement comparison
- compare expected fossil shape/hash fields with actual emitted packets
- print structured pass/fail JSON summary.

Step 4: Add tests with fixtures
- Create: `tests/test_hive_replay_verify.py`
- Create: `tests/fixtures/hive_replay/*.json`

Step 5: Run tests
- `scripts/run_tests.sh tests/test_hive_replay_verify.py -v`
- Expected: pass for good fixture; fail for mismatch fixture.

Step 6: Commit
- `git add tools/infra/hive_replay_verify.py tests/test_hive_replay_verify.py tests/fixtures/hive_replay`
- `git commit -m "feat: add deterministic hive replay verifier"`

## Task 7: Add queue fairness policy

Objective: Reduce starvation by introducing optional age-aware claiming.

Files:
- Modify: `tools/infra/hive_arango_queue.py`
- Modify: `tools/infra/hive_bee.py`
- Modify: `tools/infra/hive_swarm.py`

Step 1: Extend claim function signature
- Add `age_boost_coeff: float = 0.0`.

Step 2: Update AQL sort score
- Effective score = `priority + age_boost_coeff * age_minutes`.
- Keep current behavior when coeff is 0.

Step 3: Add CLI arg pass-through in bee/swarm
- `--age-boost-coeff`.

Step 4: Add tests
- Extend: `tests/test_hive_arango_queue.py` with fairness scoring scenario.

Step 5: Run tests
- `scripts/run_tests.sh tests/test_hive_arango_queue.py tests/test_hive_bee.py tests/test_hive_swarm.py -v`
- Expected: pass, deterministic ordering under test fixture.

Step 6: Commit
- `git add tools/infra/hive_arango_queue.py tools/infra/hive_bee.py tools/infra/hive_swarm.py tests/test_hive_arango_queue.py`
- `git commit -m "feat: add age-aware queue fairness policy"`

## Task 8: Refactor bee into focused modules

Objective: Lower coupling and isolate retrieval/proposal/fossilization concerns.

Files:
- Create: `tools/infra/hive_bee_retrieval.py`
- Create: `tools/infra/hive_bee_proposal.py`
- Create: `tools/infra/hive_bee_fossilize.py`
- Modify: `tools/infra/hive_bee.py`

Step 1: Move retrieval functions
- move gravity query/retrieval/summary functions.

Step 2: Move proposal functions
- move prompt builder, model call, tactic extraction.

Step 3: Move fossilization/replay functions
- move theorem generation, replay packet builders, persistence helpers.

Step 4: Keep `hive_bee.py` as orchestrator
- preserve public API used by `hive_swarm.py` and tests.

Step 5: Run tests
- `scripts/run_tests.sh tests/test_hive_bee.py tests/test_hive_swarm.py -v`
- Expected: unchanged behavior, green tests.

Step 6: Commit
- `git add tools/infra/hive_bee*.py tests/test_hive_bee.py tests/test_hive_swarm.py`
- `git commit -m "refactor: split hive bee into retrieval/proposal/fossilize modules"`

## Task 9: Add run telemetry events

Objective: Emit consistent metric events for queue/retrieval/model/lean phases.

Files:
- Modify: `tools/infra/hive_bee.py`
- Modify: `tools/infra/hive_swarm.py`
- Modify: `tools/infra/hive_arango_queue.py`

Step 1: Define minimal metric schema
- `event_kind`, `task_key`, `goal_key`, `worker_id`, `phase`, `duration_ms`, `status`.

Step 2: Emit events at each phase boundary
- retrieval, generation, critic, formalization, fossilization, recirculation.

Step 3: Persist into `hive_events` with unique keys.

Step 4: Add tests
- Extend unit tests with event assertions.

Step 5: Run tests
- `scripts/run_tests.sh tests/test_hive_bee.py tests/test_hive_swarm.py tests/test_hive_arango_queue.py -v`

Step 6: Commit
- `git add tools/infra/hive_bee.py tools/infra/hive_swarm.py tools/infra/hive_arango_queue.py tests/test_hive_*`
- `git commit -m "feat: add structured telemetry events for hive run phases"`

## Task 10: Add integration smoke lane

Objective: Validate full ingest -> queue -> worker -> replay path in one hermetic CI-style test.

Files:
- Create: `tests/integration/test_hive_e2e_smoke.py`
- Create: `tests/fixtures/hive_e2e/*`

Step 1: Build fixture-driven smoke test
- mock Arango API responses
- fixture replay packet + expected fossil output

Step 2: Assert full transition chain
- pending -> leased -> completed
- goal reaches terminal state
- replay verifier pass result.

Step 3: Run test
- `scripts/run_tests.sh tests/integration/test_hive_e2e_smoke.py -v`

Step 4: Commit
- `git add tests/integration/test_hive_e2e_smoke.py tests/fixtures/hive_e2e`
- `git commit -m "test: add hive end-to-end smoke lane"`

## Task 11: Add operator runbook for new commands

Objective: Keep operations reproducible for local and CI runs.

Files:
- Modify: `docs/HiveArchitectureBlueprint.md`
- Modify: `tools/infra/README.md`

Step 1: Add replay-verify command examples.
Step 2: Add fairness-policy usage examples.
Step 3: Add expected output snippets.

Step 4: Commit
- `git add docs/HiveArchitectureBlueprint.md tools/infra/README.md`
- `git commit -m "docs: add replay verification and fairness runbook"`

## Task 12: Final verification and push

Objective: Ensure the plan implementation remains green and publishable.

Files:
- Verify all modified files.

Step 1: Run focused hive suite
- `scripts/run_tests.sh tests/test_hive_*.py tests/integration/test_hive_e2e_smoke.py -v`

Step 2: Run repository status check
- `git status --short --branch`

Step 3: Push branch
- `git push origin fusion/upstream-intake-20260419`
- `git push upstream fusion/upstream-intake-20260419`

Step 4: Capture execution trace
- Update `docs/LeanBuildRepairProcessTrace.md` or a Hive-specific trace doc with commands/results.

---

## Acceptance criteria

- Contract docs exist and are indexed.
- Packet and queue transitions validated by code-level guards.
- Replay verifier exists, is tested, and can fail on mismatch.
- Fairness policy is optional and deterministic under tests.
- Bee module coupling reduced with unchanged external behavior.
- Telemetry events are emitted and queryable.
- E2E smoke lane passes under `scripts/run_tests.sh`.

## Execution handoff

Plan is complete and saved. Ready to execute task-by-task; I can start immediately with Task 1 and Task 2, then move through code slices with tests after each commit.
