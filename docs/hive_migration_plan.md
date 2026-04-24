# Surgical Migration Plan: Current Hive -> Greenfield Hive Architecture

Status: migration plan
Date: 2026-04-23
Depends on: `docs/hive_greenfield_architecture.md`
Related doctrine: `docs/hermes_recursive_hive_architecture.md`
Scope: current files
- `tools/infra/hive_bee.py`
- `tools/infra/hive_swarm.py`
- `tools/infra/research_digest_worker.py`
- supporting queue manifold in `tools/infra/hive_arango_queue.py`

Symbolic doctrine dependency:
- `docs/jung_alchemy_packet_doctrine.md` defines the formal
  BlackBookSource-to-PromotionDecisionPacket transmutation ladder and the
  Jungian/alchemical vocabulary used here as operational doctrine, not proof
  authority.

## 0. Executive summary

The current Hive is not wrong. In fact, it already contains several strong architectural decisions that should be preserved:
- separate Arango lanes (`8529` for theorem DAG, `8530` for Alexandria/Hive)
- strong-gravitation before proof attempts
- Lean-only proof authority
- fossilization and deadend recording
- explicit separation of `research-digest` from proof bees
- early emergence of generator / critic / formalizer / auditor role distinction

The problem is not the philosophy. The problem is that too many planes are still collapsed into worker implementations.

Therefore the migration strategy should be surgical, not destructive:
- keep the trust boundary,
- keep the existing collections where possible,
- keep working smoke flows alive,
- introduce typed packet/task/resource structure incrementally,
- do not freeze development waiting for a total rewrite.

## 1. Current-state audit

## 1.1 `tools/infra/hive_arango_queue.py`

Current strengths:
- already acts as MotherBee manifold/queue substrate
- has schema init
- has heartbeats
- has claim/complete/fail operations
- already distinguishes docs vs edge collections
- already has useful queue helpers and status surfaces
- already records `hive_replay_packets` in schema, which is an excellent foundation

Current limitations:
- task typing is still too generic
- resource leasing is not first-class
- packet lineage edges are still too thin
- queue state must often be inferred from worker behavior rather than packet state
- build/resource waiting is external to the manifold

Verdict:
- keep as the foundational control-plane substrate
- extend rather than replace

## 1.2 `tools/infra/hive_bee.py`

Current strengths:
- excellent trust-boundary discipline
- retrieval before proposal
- Lean proof state before prompt
- Lean verification instead of model self-certification
- real fossil capture via `HiveLogos` and generated theorem snippet
- deadend recording
- partial blocker inference
- good artifact writing behavior

Current weaknesses:
- retrieval, proposal, verification, fossilization, and failure analysis are all inside one worker
- too much orchestration logic lives in the worker
- retrieval is recomputed inline instead of being reusable packet output
- generated theorem capture and queue mutation are tightly coupled
- proof bee still owns too many state transitions directly

Verdict:
- preserve as canonical proof-lane semantics
- split operationally into smaller worker families over time
- do not rewrite its semantics first; extract them

## 1.3 `tools/infra/hive_swarm.py`

Current strengths:
- already contains explicit role split:
  - generator
  - critic
  - formalizer
  - auditor
- suggests the right eventual architecture
- records structured run artifacts
- keeps proof authority downstream of critique and verification

Current weaknesses:
- multiple cognitive roles still live in one process/script
- swarm run packet is local and useful, but not yet fully normalized into Hive packet families
- role separation exists logically, not infrastructurally
- not yet wired into a more general MotherBee dependency graph

Verdict:
- keep as an incubator for role semantics
- do not treat as the final architecture
- use it to derive packet schemas for proposal/critique/audit workers

## 1.4 `tools/infra/research_digest_worker.py`

Current strengths:
- very important separation from proof bees
- correctly treats `research-digest` as non-Lean work
- integrates Alexandria fetch/ingest/retrieve pipeline
- writes back completion/failure into Hive
- already handles special context tasks such as `MotherBeeContext`

Current weaknesses:
- fetch/digest/retrieve/packetization are still bundled
- outputs are not yet normalized as first-class theorem-candidate packets
- too much path/runner knowledge lives in the worker code
- not yet integrated with a general transition from research output to proof queue input

Verdict:
- keep the lane separation
- extract its outputs into reusable research packet schemas
- eventually split into fetch / digest / packetize worker families if scale justifies it

## 2. Migration principles

1. No loss of current working smoke flows.
2. Never break the Lean trust boundary.
3. Introduce typed packets first, role explosion later.
4. Move orchestration into MotherBee before splitting more workers.
5. Surface build/resource waiting in Hive state as early as possible.
6. Preserve replay and deadend residue as central memory.
7. Preserve symbolic source material before attempting formalization.
8. Type symbolic material as theorem candidates before proof workers may consume it.
9. Treat analytic-psychology language as operational vocabulary for symbolic pressure, integration, and failure modes; never as proof authority.
10. Fail closed on authority inflation, source repression, or shadow/owner confusion.

## 3. Target migration phases

The next coding pass should follow the categorical/lambda packet doctrine from the greenfield spec:
- packets are typed objects,
- workers are morphisms,
- authority gates are certifying morphisms,
- Phase 1 should therefore make packet schemas and invariants executable before splitting workers.

## Phase 1: Task typing and explicit packet schemas

Goal:
- keep current workers mostly intact
- make their inputs/outputs explicit and typed

Changes:
1. Add `task_kind` to `hive_tasks`.
2. Add packet metadata fields:
   - `authority`
   - `representation_class`
   - `representation_depth`
3. Add `ExecutionIntentPacket` and `PromotionDecisionPacket` schema support.
4. Add `result_kind` / packet kind metadata to emitted artifacts.
5. Introduce new collections:
   - `hive_retrieval_packets`
   - `hive_proposals`
   - `hive_critiques`
   - `hive_verifications`
   - `hive_build_packets`
   - `hive_audit_packets`
   - `hive_candidate_packets`
6. Add edges:
   - `hive_task_emits_packet`
   - `hive_task_consumes_packet`
   - `hive_packet_depends_on`
7. Encode hard invariants at the schema/helper layer:
   - `ResearchDigestPacket` cannot assert theorem closure
   - `TheoremCandidatePacket` is intent, not evidence
   - `VerificationPacket` requires `ExecutionIntentPacket`
   - `FossilPacket` requires successful verification
   - `BuildPacket` is the only compilation authority
   - `PromotionDecisionPacket` is separate from build/fossil outputs
   - shadow packets cannot discharge owner debts without an explicit bridge path
   - symbolic source packets must preserve source references before distillation
   - candidate packets derived from symbolic/Black Book material must carry `symbolic_origin`
   - packet authority overclaim is rejected as `semantic_blocked`
   - missing symbolic provenance is rejected as `source_repression`
   - `representation_class = shadow` with owner-debt discharge intent is rejected unless an explicit bridge packet is present

Implementation strategy:
- keep `hive_bee.py` behavior, but make it write explicit retrieval/proposal/verification packet docs before it completes the task
- keep `research_digest_worker.py` behavior, but make it write explicit retrieval/research packet docs
- add `validate_packet_invariants(...)` checks for the symbolic-source / authority / representation rules before packet insertion

Benefits:
- replay becomes easier
- observability becomes clearer
- later worker splitting becomes far simpler

Risk:
- low

## Phase 2: Retrieval as a first-class worker output

Goal:
- stop embedding graph retrieval as an invisible pre-step in proof bees

Changes:
1. Create `graph.retrieve` task kind.
2. Retriever worker produces retrieval packets.
3. Proof bees consume retrieval packet refs instead of directly calling gravity first.
4. Retrieval packet explicitly records:
   - graph source (`8529`, jsonl fallback, stale snapshot)
   - freshness
   - SCC anchors
   - raw witnesses
   - outage flags

Implementation strategy:
- first, let `hive_bee.py` call a new internal helper that stores retrieval packet docs before proceeding
- later, allow MotherBee to enqueue retrieval as an upstream dependency

Benefits:
- cacheability
- better outage reporting
- lower duplicate compute
- better support for audit and replay

Risk:
- low to medium

## Phase 3: Proof-state, proposal, and verification packetization

Goal:
- decouple cognitive stages without immediately multiplying scripts

Changes:
1. `hive_bee.py` should emit:
   - proof-state packet
   - proposal packet
   - verification packet
2. `hive_swarm.py` should normalize generator/critic/auditor outputs into those same packet families
3. MotherBee should treat these as reusable packet types regardless of which worker generated them

Implementation strategy:
- do not split executables yet
- just normalize data model and collection writes

Benefits:
- unified audit trail
- same schema across single-bee and swarm-bee modes
- easier future role splitting

Risk:
- medium

## Phase 4: Build/resource state becomes first-class

Goal:
- stop inferring wait/running state from terminal messages

Changes:
1. Add collections:
   - `hive_resources`
   - `hive_resource_leases`
2. Add `build.locked` task kind.
3. Represent these states explicitly:
   - `queued`
   - `lock_wait`
   - `running`
   - `passed`
   - `failed`
   - `environment_blocked`
4. Build worker becomes the only component allowed to run locked Lake builds.

Implementation strategy:
- start by wrapping the current `run_locked_lake_build.py` behavior in a build task updater
- do not remove the script; make the script a backend for a build worker

Benefits:
- eliminates ambiguity about whether a job is waiting or running
- supports dashboards and notifications from Hive state rather than terminal noise

Risk:
- medium

## Phase 4.5: Lineage inspection becomes operational

Goal:
- make the packet graph inspectable before adding more autonomous behavior

Initial CLI surface:
- `python3 tools/infra/hive_arango_queue.py show-packet --packet-key <PACKET>`
- `python3 tools/infra/hive_arango_queue.py lineage-upstream --packet-key <PACKET> --depth 4`
- `python3 tools/infra/hive_arango_queue.py lineage-downstream-task --task-key <TASK> --depth 4`

Purpose:
- inspect authority ancestry from promotion back to audit/build/verification
- inspect packets emitted by a task
- debug synthetic-smoke containment and fail-closed lineage

This is read-only operability.  It does not replace Lean/build/audit authority.

## Phase 4.6: Origin metadata is normalized across authority gates

Goal:
- prevent synthetic/test lanes, theorem-lane packets, research material, and
  symbolic Black Book material from becoming indistinguishable inside lineage

Required normalized fields:
- `source_regime`: `symbolic` | `research` | `theorem_lane` | `synthetic_smoke` | `infrastructure` | `unknown`
- `verification_origin`: `lean_produced` | `synthetic_smoke` | `replay_lane` | `unknown`
- `build_origin`: `locked_lake_build` | `synthetic_smoke` | `unknown`
- `audit_origin`: `auditbee` | `manual` | `synthetic_smoke` | `unknown`
- `promotion_origin`: `promotionbee` | `manual` | `unknown`

Implementation status:
- `validate_packet_invariants(...)` normalizes missing origin metadata with
  conservative defaults;
- `hive_bee.py` marks Lean verification packets as `lean_produced`;
- replay packets are marked as `replay_lane`;
- `hive_build_worker.py` marks build packets as `locked_lake_build`;
- `hive_audit_worker.py` marks AuditBee packets and carries synthetic-smoke
  source regime forward when applicable;
- `hive_promotion_worker.py` marks PromotionBee packets and preserves synthetic
  smoke containment.

This is an anti-inflation control.  A synthetic packet chain may demonstrate
infrastructure health, but it must remain visibly separate from theorem-lane
authority.

## Phase 4.7: Transport-controlled cognition

Goal:
- support real researcher access patterns without baking API privilege into the
  Hive architecture
- avoid many cold direct provider/API connections by default

Default provider-contact policy:
- route provider contact through one persistent Codex CLI-backed worker when
  possible;
- let Hive communicate with that instantiated worker repeatedly;
- treat direct provider API calls as explicit exceptions.

Provider outage classification:
- `blocked_kind = provider_unavailable`
- `status = environment_blocked`
- `failure_kind = retryable_transport_failure`
- `semantic_failure = false`
- `proof_failure = false`

Recovery rule:
- do not fan out to additional direct provider/API endpoints;
- do not switch model/endpoint on the system's own authority;
- pause aggressive retries;
- restart or resume one canonical Codex CLI-backed agent session and continue
  through Hive.

Allowed cognition transports:
- subscription-backed Codex CLI as the default provider-contact backend;
- Copilot CLI;
- guarded Gemini CLI;
- local OpenAI-compatible endpoints.
- direct provider API only with explicit override.

Backend metadata on proposal-side packets:
- `backend_kind`
- `backend_identity`
- `subscription_backed`
- `model_name`
- `backend_capability`
- `provider_contact_policy`

Hard invariant:
- cognition backends may emit proposal/candidate/research packets;
- cognition backends must not directly emit verification/build/audit/promotion
  packets.

Codex CLI should be treated as the stricter coding/review/code-transform backend.
Copilot CLI and guarded Gemini CLI can be useful symbolic interpolation
backends, but their output still remains below the authority gates.

Hardware/local-model law:
- DGX Spark-class local hardware supports the Hive, but does not replace the
  agentic condensation phase;
- do not make a local large-context monomodel the primary design target;
- coding agents are structurally necessary because condensation is code-aware
  compression into files, diffs, imports, syntax, and executable proof surfaces.

Implementation status:
- proof-bee proposal packets carry backend metadata;
- proof-bee proposal, critique, and execution-intent packets carry `hermes_role`;
- direct `provider_api` proposal calls are disabled by default and require an
  explicit `--allow-direct-provider-api` flag.
- proof-bee model/backend exceptions now mark the task and goal as
  `environment_blocked` with `provider_unavailable` /
  `retryable_transport_failure`, not as semantic deadends.

## Phase 4.8: Negative antiproofs as structured resistance memory

Goal:
- upgrade deadends from generic failure records into reusable no-go witnesses

A negative antiproof certifies that one candidate passage does not close:
- for a definite reason,
- at a definite authority level,
- in a definite corridor,
- with explicit downstream transitions blocked by that failure.

It must not overclaim global impossibility unless a future owner-level theorem
actually proves such a no-go.

Deadend/antiproof metadata:
- `antiproof_kind`
- `authority_level`
- `corridor`
- `forbids_downstream`
- `global_impossibility_claim`

Initial antiproof kinds:
- `proposal_rejection`
- `lean_nonclosure`
- `build_nonintegration`
- `audit_nonpromotion`
- `owner_shadow_conflict`
- `synthetic_anchor_only`
- `environment_blocked`
- `missing_owner_theorem`

Implementation status:
- proof-bee deadends now record `lean_nonclosure` antiproof metadata and
  explicitly forbid build/audit/promotion downstream for that failed path.
- AuditBee now walks upstream build lineage to inspect proposal backend,
  Hermes role, provider-contact policy, representation class, verification
  origin, and owner/shadow bridge legitimacy.
- `hive_arango_queue.py backend-trace --packet-key <PACKET>` summarizes
  authority/backend/Hermes metadata along upstream packet lineage.

Doctrine:
- proofs are positive condensates;
- negative antiproofs are structured phase-stability failures;
- expertise is successful closure plus remembered failed closure routes.

## Phase 5: TheoremCandidatePacket bridge from research/Black Book to proof queue

Goal:
- make the constitutional bridge explicit
- make the reconciliation of symbolic material and logos discipline operational

Changes:
1. Add collection:
   - `hive_candidate_packets`
2. Research workers emit `TheoremCandidatePacket` rather than loosely structured output
3. MotherBee decides whether a candidate becomes:
   - `proof.search`
   - `audit.semantic`
   - `future_pass_only`
4. Candidate packets derived from Black Book / symbolic material must include:
   - `symbolic_origin`
   - preserved source reference
   - `representation_class`
   - `representation_depth`
   - owner/translator/coherence candidates
   - remaining proof obligations
   - no-fake-closure declaration

Implementation strategy:
- current `research_digest_worker.py` can emit candidate packets after retrieval
- Black Book/future-pass tooling can also target the same schema
- MotherBee should reject candidates that suppress source provenance or attempt to promote symbolic content directly to proof work

Benefits:
- keeps future-pass and formal ledger separate
- gives one legal bridge into proof queue
- matches repo doctrine exactly
- prevents both symbolic repression and theorem-authority inflation

Risk:
- low

## Phase 6: Actual worker family split

Goal:
- split along natural seams only after schema is stable

New executables:
- `hive_retriever.py`
- `hive_proposal_bee.py`
- `hive_critic_bee.py`
- `hive_lean_executor.py`
- `hive_fossil_bee.py`
- `hive_audit_bee.py`
- optional `hive_build_worker.py`

Important note:
- `hive_swarm.py` can remain as a composite worker for experimentation, but production flows should increasingly use smaller workers.

Risk:
- medium to high if done too early
- therefore this is a late phase

## 4. Specific code changes I would make first

These are the first concrete edits I would prioritize.

### 4.1 Extend queue schema in `hive_arango_queue.py`

Add document collections:
- `hive_retrieval_packets`
- `hive_proposals`
- `hive_critiques`
- `hive_verifications`
- `hive_build_packets`
- `hive_audit_packets`
- `hive_candidate_packets`
- `hive_promotions`
- `hive_resources`
- `hive_resource_leases`

Add indexes:
- by `goal_key`
- by `task_key`
- by `packet_sha`
- by `task_kind`
- by `authority`
- by `representation_class`
- by `resource_class`
- by `status`

Add helper functions:
- `enqueue_task(...)` with explicit `task_kind`
- `import_packet(...)`
- `validate_packet_invariants(...)`
- `claim_resource(...)`
- `release_resource(...)`
- `list_waiters(...)`

### 4.2 Refactor `hive_bee.py`

Without changing the trust boundary, factor its internals into explicit stages:
- `produce_retrieval_packet(...)`
- `produce_proof_state_packet(...)`
- `produce_proposal_packet(...)`
- `produce_verification_packet(...)`
- `produce_deadend_packet(...)`
- `produce_fossil_and_replay_packets(...)`

Then the current single-bee workflow still works, but now writes packet objects that future workers can consume.

### 4.3 Refactor `hive_swarm.py`

Normalize outputs to the same packet families:
- generator -> proposal packet
- critic -> critique packet
- formalizer -> verification packet
- auditor -> audit packet

The key is schema unification, not immediate splitting.

### 4.4 Refactor `research_digest_worker.py`

Have it emit:
- retrieval packet
- research packet
- candidate packet

Add explicit output state:
- `ready_for_proof`
- `future_pass_only`

This lets MotherBee decide next action rather than burying that logic inside the worker.

## 5. What should not be changed yet

1. Do not remove `run_locked_lake_build.py`.
   - wrap it, do not replace it immediately.

2. Do not remove generated theorem fossilization from `hive_bee.py`.
   - this is one of the best parts of the current architecture.

3. Do not merge research and proof workers again.
   - the split is correct and should get stronger.

4. Do not move Hive state into the theorem DAG DB.
   - the dual-Arango split is right.

5. Do not let proposal/critic outputs become proof truth.
   - Lean remains final.

## 6. Migration checkpoints

After each phase, require a smoke test.

### Checkpoint A: packetized current workers
- existing smoke tests still pass
- current bee loop still closes a trivial goal
- new packet collections are populated

### Checkpoint B: retrieval packets
- proof worker can consume a preexisting retrieval packet
- graph outage is represented explicitly in retrieval packet state

### Checkpoint C: build/resource state
- a locked build can be seen in Hive as `lock_wait` or `running`
- user no longer has to infer build state from delayed terminal watch messages

### Checkpoint D: candidate packet bridge
- a research task can produce a theorem candidate packet
- MotherBee can enqueue proof work from that packet

## 7. Suggested file outputs for this migration

New docs:
- `docs/hive_greenfield_architecture.md`
- `docs/hive_migration_plan.md`

Likely future code files:
- `tools/infra/hive_packets.py`
- `tools/infra/hive_resources.py`
- `tools/infra/hive_retriever.py`
- `tools/infra/hive_build_worker.py`

Potential future tests:
- `tests/test_hive_packets.py`
- `tests/test_hive_resource_leases.py`
- `tests/test_hive_retriever.py`
- `tests/test_hive_build_worker.py`

## 8. Final recommendation

If this repo keeps growing, the Hive should evolve in this order:

1. normalize schemas
2. externalize state transitions
3. make resources first-class
4. packetize research/formal bridges
5. only then split workers further

That is the least disruptive path from the current codebase to the greenfield architecture.

## 9. Bottom line

The current Hive already has the right spirit:
- strong gravitation
- Lean truth boundary
- queue-backed work
- fossilization
- deadend memory
- research/proof separation

The surgical improvement is to turn that spirit into explicit packet architecture and explicit control-plane state.

Do that first, and the rest of the worker ecosystem can evolve without losing trust-boundary discipline.
