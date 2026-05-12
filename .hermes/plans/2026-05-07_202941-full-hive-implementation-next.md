# Next steps toward full Hive implementation

## Current state

Current HEAD: `0980f328 Emit Leanstral autoproof trace packets`.

The repo now has the core bounded proof episode lane:

- `BeeTask(leanstral.autoproof)` for `HermesLeanstralBee`.
- Proposal-only inner Leanstral recurrence.
- Standalone `RepairAttemptPacket` per attempt.
- Standalone `AutoproofTracePacket` per episode.
- Final `TheoremCandidatePacket` or `ResiduePacket`.
- `BeeResult` records all emitted packet ids/hashes.
- `HermesLeanstralBee` remains proposal-only and cannot emit gate packets.

The next work should turn this from trace-producing proof episodes into a routed theorem factory with enrichment, gates, and audit promotion.

## Phase 1: MotherBee consumes trace frontier fields

Goal: make scheduler decisions use the new attempt/trace packets, not just final residue/candidate packets.

Files likely to change:

- `tools/infra/hive_motherbee.py`
- `tests/test_hive_motherbee.py`
- possibly `tools/schema/hive/BeeTask.schema.json`

Implementation:

1. Add helpers to read the newest `AutoproofTracePacket` for a lineage/target.
2. Extract routing fields:
   - `frontier.last_error_signature`
   - `frontier.failed_strategies`
   - `frontier.missing_lemmas`
   - `frontier.next_recommended_bee`
   - `frontier.new_information_needed`
3. Prefer enrichment task creation when trace says retry needs external signal:
   - unknown identifier / missing instance -> `RetrieverBee`
   - type mismatch / unsolved goals -> `SocratesBee`
   - suspicious overclaim / repeated degeneracy -> `PauliBee`
4. Keep direct exhausted residue -> `HermesLeanstralBee` blocked unless new external packet arrives after the trace/residue.
5. Add tests proving:
   - trace frontier routes to Retriever/Socrates/Pauli as appropriate.
   - repeated same error does not blindly reschedule Leanstral.
   - new Retrieval/Socratic/Pauli packet after trace re-enables Leanstral.

Verification:

```bash
.venv-py312/bin/python -m pytest tests/test_hive_motherbee.py tests/test_hive_leanstral_bee_worker.py -q
```

## Phase 2: RouteInvocationPacket

Goal: record why MotherBee emitted each BeeTask.

New schema:

- `tools/schema/hive/RouteInvocationPacket.schema.json`

Files likely to change:

- `tools/infra/hive_packet_validate.py`
- `tools/infra/hive_motherbee.py`
- `tests/test_hive_route_invocation_schemas.py`
- `tests/test_hive_motherbee.py`

Packet should record:

- source packet ids
- selected role/task kind
- skipped roles and reasons
- policy predicate values
- trace frontier inputs used
- new-signal decision
- created BeeTask id
- authority: `navigation` or `semantic`, not proof authority
- `promotion_allowed: false`

Why this matters:

MotherBee becomes auditable: not just what task was emitted, but why.

## Phase 3: LeanGate lane

Goal: separate local proof-search evidence from official Lean verification authority.

New/updated surfaces:

- `LeanVerificationPacket.schema.json` if not complete.
- `tools/infra/hive_lean_gate.py` or equivalent small runner.
- Tests for candidate -> LeanVerificationPacket.

Inputs:

- `TheoremCandidatePacket`
- optionally `AutoproofTracePacket`
- optionally accepted `RepairAttemptPacket`

Outputs:

- `LeanVerificationPacket` with `authority = lean_checked`

Rules:

- Only `LeanBee`/LeanGate may emit `LeanVerificationPacket`.
- It must run current Lean tooling, not trust the wrapper trace alone.
- If it uses `lake build`, use the repo lock wrapper where appropriate:
  `tools/infra/run_locked_lake_build.py --wait-for-build-lock <Module>`.

Tests:

- HermesLeanstralBee still rejected for `LeanVerificationPacket`.
- LeanBee requires appropriate input.
- LeanGate emits lean_checked only after actual Lean command success.

## Phase 4: BuildGate, AuditGate, PromotionGate

Goal: implement the authority ladder end-to-end.

Sequence:

```text
TheoremCandidatePacket
  -> LeanVerificationPacket
  -> BuildPacket
  -> AuditPacket
  -> PromotionDecisionPacket
```

Implementation priority:

1. BuildGate: validates module/build command and emits `BuildPacket`.
2. AuditGate: routes Pauli/Goedel/Nemotron-style audit result into `AuditPacket`.
3. PromotionGate: only promotes if Lean + build + audit records all pass.

Tests:

- No gate skips prior gate.
- Authority enum increases only in the correct role.
- Promotion blocked by missing audit or failed build.

## Phase 5: Enrichment bees

Goal: make residues active frontiers, not dead ends.

Implement minimal deterministic workers first:

- `RetrieverBee`: emits `RetrievalHypothesisPacket` from missing lemmas/error signatures.
- `SocratesBee`: emits `SocraticQuestionPacket` for type mismatch / missing hypothesis / ambiguous theorem shape.
- `PauliBee`: emits `PauliCritique` for authority inflation, owner-shadow confusion, repeated degenerate proof attempts.

Tests:

- Each emits only allowed authority/kinds.
- Each can provide “new external signal” for a later Leanstral retry.
- No enrichment bee can emit Lean/build/audit/promotion authority.

## Phase 6: DAG/Arango projection

Goal: project packet lineage for navigation without making Arango authority.

Inputs:

- BeeTask
- RepairAttemptPacket
- AutoproofTracePacket
- RouteInvocationPacket
- Candidate/Residue/Gate packets

Rules:

- append-only JSONL remains Hive memory source.
- Arango is derived navigation/projection.
- projection edges must preserve packet ids and hashes.

## Recommended immediate next commit

Commit title:

```text
Route autoproof frontiers from trace packets
```

Scope:

- `hive_motherbee.py`
- `tests/test_hive_motherbee.py`

Do not add new packet schemas in this commit unless absolutely necessary.

Acceptance criteria:

- MotherBee reads standalone `AutoproofTracePacket`.
- MotherBee uses frontier fields for enrichment routing.
- Exhausted residue still cannot self-loop into Leanstral without new external signal.
- New Retrieval/Socratic/Pauli signal after the trace re-enables Leanstral.

Validation:

```bash
.venv-py312/bin/python -m pytest \
  tests/test_hive_motherbee.py \
  tests/test_hive_leanstral_bee_worker.py \
  tests/test_hive_autoproof_trace_schemas.py \
  tests/test_hive_bee_runner.py -q
```

## Key invariant to preserve

```text
Inside one BeeTask:
  Lean feedback is new information.
  Bounded recurrence is mandatory.

Across exhausted BeeTasks:
  residue/trace alone is not new information.
  retry requires Socratic, Pauli, Retrieval, Translation, candidate, owner, or operator signal.

Trace packets are evidence, not authority.
LeanGate alone emits LeanVerificationPacket.
```
