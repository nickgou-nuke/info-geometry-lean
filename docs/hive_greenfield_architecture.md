# Greenfield Hive Architecture for info-geometry-lean-fusion

Status: design document
Date: 2026-04-23
Scope: greenfield architecture for the Hive / MotherBee / bee-worker ecosystem, informed by the current codebase, acquired skills, and repo-operational memory.

## 0. Why this redesign is needed

The current Hive code already contains the seeds of the right architecture:
- `tools/infra/hive_arango_queue.py` provides a queue/manifold layer on the Alexandria Arango instance (`8530`), separate from the theorem DAG Arango instance (`8529`).
- `tools/infra/hive_bee.py` enforces a strong trust boundary: retrieve graph context first, get Lean proof state, propose a tactic, verify through Lean, fossilize success, record deadends on failure.
- `tools/infra/hive_swarm.py` already reveals a role split: generator, critic, formalizer, auditor.
- `tools/infra/research_digest_worker.py` correctly separates `research-digest` from theorem-proving tasks and routes those tasks through Alexandria ingestion/retrieval instead of Lean.

But the current implementation still mixes too much orchestration into workers:
- retrieval is embedded inside proof workers rather than becoming a reusable packet-producing service;
- build/resource contention is externalized into ad hoc scripts rather than represented as first-class Hive state;
- task typing is still too implicit;
- proofs, research, audits, and build verification are not yet separated into explicit pipeline families;
- replay and residue are present in spirit, but not yet central to the operational design.

This document describes the architecture I would build on a green field for this repository.

It is explicitly shaped by the repo's durable constraints:
- Lean is the only proof authority.
- the theorem DAG / proof graph remains on `8529`.
- Alexandria semantic digestion remains on `8530`.
- operatorial, noncommutative, dimension-agnostic trunk ownerhood comes first;
- scalar / finite / diagonal lanes are shadows and must never be allowed to silently replace the trunk.

## 1. Governing doctrine

The Hive should not be thought of as "some agents calling Lean".

It should be thought of as a packetized theorem-factory operating system.

That means:
- every action emits a typed packet,
- every packet has provenance,
- every state transition is explicit,
- every theorem claim is routed through Lean,
- every promotion is routed through audit,
- every failure becomes structured residue,
- every shadow packet remains marked as a shadow.

For the formal symbolic-to-packet doctrine behind this operating model, see
[`docs/jung_alchemy_packet_doctrine.md`](jung_alchemy_packet_doctrine.md).  That
note is the stable bridge between Black Book / Jungian-alchemical discovery
language and the packet authority ladder used here.

For the recursive worker ontology, see
[`docs/hermes_recursive_hive_architecture.md`](hermes_recursive_hive_architecture.md).
That note defines `Hermes[backend]` workers such as `Hermes[CodexCLI]`,
`Hermes[GeminiCLI]`, and `Hermes[CopilotCLI]` as backend embodiments of a
shared Hermes packet/memory/skill discipline.

## 1.1 Categorical / lambda-calculus reading

The clean abstraction for this repository is categorical.

- packet = typed object
- worker = morphism
- authority gate = certifying/effectful morphism
- pipeline = composition
- replay = cached normal form
- deadend = failed reduction trace
- promotion = terminal accepted object in a privileged subcategory

A canonical packet flow is:

```text
BlackBookSource
  --distill-->
TheoremCandidatePacket
  --retrieve-->
RetrievalPacket
  --proof_state-->
ProofStatePacket
  --propose-->
ProposalPacket
  --critic-->
ExecutionIntentPacket
  --lean_verify-->
LeanVerificationPacket
  --build_verify-->
BuildPacket
  --audit-->
AuditPacket
  --promote-->
PromotionDecisionPacket
```

The same flow can be read as a typed lambda-calculus discipline:

```text
distill    : BlackBookSource -> TheoremCandidatePacket
retrieve   : TheoremCandidatePacket -> RetrievalPacket
proofState : TheoremCandidatePacket -> ProofStatePacket
propose    : ProofStatePacket × RetrievalPacket -> ProposalPacket
critic     : ProposalPacket -> ExecutionIntentPacket
leanVerify : ExecutionIntentPacket -> LeanVerificationPacket
buildVerify: LeanVerificationPacket -> BuildPacket
audit      : BuildPacket -> AuditPacket
promote    : AuditPacket -> PromotionDecisionPacket
```

The authority gates are not ordinary morphisms. They are certifying morphisms:
- Lean turns execution intent into proof-checked output
- build turns Lean-checked output into compilation-checked output
- audit turns build-checked output into semantically accepted output

So the Hive is best viewed as a category of packets with constrained morphisms and authority-stratified subcategories such as:
- `C_navigation`
- `C_semantic`
- `C_proposal`
- `C_execution`
- `C_authority`
- `C_promotion`

The governing doctrine then becomes:
- only morphisms in `C_authority` may increase packet authority level;
- only audit/promotion morphisms may move an object into `C_promotion`;
- shadow objects cannot discharge owner objects unless an explicit bridge morphism exists.

## 1.2 Psychological correspondence

The same architecture has a useful analytic-psychology reading.  This is not a
clinical claim and not mathematical authority; it is operational vocabulary for
how symbolic material is preserved, typed, tested, and integrated.

```text
common unconscious
  = shared symbolic reservoir, Black Book, dreams, analogies, latent theorem forms

anima
  = mediating image-function that gives unconscious material a form the ego can encounter

ego
  = local task focus, current proof goal, operational attention

logos
  = typed packet discipline, Lean authority, build/audit gates

Self
  = the larger integrated theorem organism / repo totality
```

MotherBee sits near the ego/Self boundary.  It does not create the symbolic
material and it does not itself prove truth.  It mediates:

```text
unconscious image
  -> anima-symbolic form
  -> ego attention
  -> typed packet
  -> logos verification
  -> integrated memory
```

The failure modes have direct engineering translations:

```text
inflation
  = accepting symbolic/prose insight as theorem truth
  = packet authority overclaim

repression
  = discarding symbolic material because it is not yet formal
  = failure to preserve symbolic source

shadow confusion
  = finite/scalar proxy pretending to be operatorial ownerhood
  = representation_class / representation_depth mismatch

individuation
  = promoted theorem integrated with provenance
  = authority-gated packet lineage ending in an audited promotion decision
```

The operational rule is therefore:
- every symbolic source must be preserved;
- every symbolic source must be typed before use;
- every typed candidate must pass authority gates before promotion;
- every shadow must remain marked as shadow unless an explicit bridge promotes it;
- the unconscious may generate candidates, but only logos may integrate them into theorem memory.

## 2. Top-level architectural split

The greenfield Hive has 4 planes.

### 2.1 Control plane

Responsibilities:
- queue management
- task scheduling
- lease / retry / backoff policy
- worker registration and heartbeat
- resource arbitration
- promotion gating
- operational observability

Canonical component:
- `MotherBee`

Critical rule:
- MotherBee does not generate mathematics and does not prove theorems.
- MotherBee only controls motion through the system.

### 2.2 Cognition plane

Responsibilities:
- retrieval synthesis
- theorem candidate packetization
- tactic proposal
- critique
- research digestion
- symbolic distillation
- semantic audit

Critical rule:
- cognition may propose, rank, reject, or refine;
- cognition never closes a theorem on its own.

### 2.2.1 Transport-controlled cognition

The Hive must not assume that every researcher has direct provider API budget.
Many researchers have a ChatGPT subscription with Codex CLI access, or a
different subscription-backed CLI, rather than raw API access. Therefore the
cognition plane should abstract over agent transport.

Default provider-contact policy:
- provider contact should be routed through one persistent Codex CLI-backed
  agent instance when possible;
- the Hive should communicate repeatedly with that instantiated worker rather
  than opening many cold direct provider/API connections;
- direct provider API calls are exceptional and must be explicit, not default.

Provider outage discipline:
- provider/API outage is `provider_unavailable`, `environment_blocked`, and
  `retryable_transport_failure`;
- it is not a proof failure, not a semantic deadend, and not evidence against
  the theorem candidate;
- the Hive must not respond by fanning out to more direct cold provider
  connections;
- the correct recovery path is to pause aggressive retries, restart or resume
  one canonical Codex CLI-backed session, and continue through Hive.

Allowed cognition transports include:
- subscription-backed Codex CLI as the default provider-contact backend;
- Copilot CLI;
- guarded Gemini CLI;
- local OpenAI-compatible endpoints;
- local or remote research-specific model services;
- direct provider API only as an explicit override.

These backends are first-class proposal engines, not authority engines.

Backend metadata should be attached to proposal-side packets:
- `backend_kind`: `provider_api` | `codex_cli` | `copilot_cli` | `gemini_cli` | `local_openai_compatible`
- `backend_identity`
- `subscription_backed`: boolean
- `model_name`
- `backend_capability`: `strict_code_review` | `code_transform` | `symbolic_interpolation` | `research_digest`
- `provider_contact_policy`: normally `codex_cli_only_for_provider_contact`

Operational distinction:
- Codex CLI is usually the stricter coding/review/code-transform backend.
- Copilot CLI and guarded Gemini CLI can be useful symbolic interpolators for
  generalized mathematical representation search.
- none of these backends may certify theorem truth or semantic promotion.

Thermodynamic reading:
- Copilot CLI and guarded Gemini CLI are hot-side symbolic-pressure backends;
- Codex CLI is the colder compression/review backend;
- uncondensed valuable material becomes residue, not deletion.

Hardware/local-model law:
- DGX Spark-class local hardware is valuable for memory, retrieval, local
  inference, and graph/Lean tooling;
- it is not enough reason to centralize the Hive into one large-context local
  monomodel;
- the condensation phase is code-aware compression, not merely long-context
  reasoning;
- coding agents are therefore mandatory condensation backends, not optional
  garnish.

Repo witnesses for this reading:
- `lean/SelfReference/RobustThermodynamicRegression.lean` formalizes
  fluctuation pressure, stiffness, and phase-transition instability for the
  thermofit lane;
- `tools/infra/llm_thermo_conformance.py` audits runtime LLM thermo traces;
- `docs/policy/agentic_soul.md` gives the loop
  `generate -> condense -> lock -> calcine -> fail or prove`.

Hard rule:
- agent backends may emit `ProposalPacket`, `CritiquePacket`,
  `TheoremCandidatePacket`, or research/digest packets;
- agent backends must not directly emit `LeanVerificationPacket`,
  `BuildPacket`, `AuditPacket`, or `PromotionDecisionPacket`.

In short: the Hive abstracts over authority less than over transport.  Transport
may vary, but provider contact should be consolidated through Codex CLI by
default. Authority remains Lean/build/audit/promotion.

### 2.3 Execution plane

Responsibilities:
- Lean proof-state calls
- Lean tactic execution
- generated theorem capture
- locked builds
- file/artifact generation
- indexing/fossilization

Critical rule:
- execution is deterministic or as deterministic as practical;
- execution does not choose policy;
- execution only runs the job it is given.

### 2.4 Storage plane

Responsibilities:
- graph packet store
- append-only event store
- artifact filesystem
- replay/residue storage
- retrieval caches

Critical rule:
- proof truth remains in Lean, not in Arango;
- Hive stores packet provenance and operational memory, not mathematical authority.

## 3. Hard separation of Arango roles

This is already latent in the repo and should become constitutionally explicit.

### 3.1 Arango on `8529`: theorem DAG / proof graph / operational graph memory

Role:
- source/decl graph
- SCC/topology/witness navigation
- gravitational context for theorem corridors
- raw-proof navigation, not semantic ingestion authority

Use cases:
- `graph.retrieve`
- theorem corridor navigation
- owner/translator/coherence adjacency
- raw witness descent

### 3.2 Arango on `8530`: Alexandria semantic lane + Hive manifold

Role:
- semantic digestion and retrieval
- research-digest storage
- theorem packet library
- Hive queue/manifold state

Use cases:
- `research.digest`
- `theorem.packetize`
- live Hive task/event/worker collections

Hard rule:
- do not mix Hive queue state into the theorem DAG database;
- do not treat Alexandria semantic retrieval as proof authority.

## 4. First-class packet model

Every pipeline stage should emit an immutable typed packet.

## 4.1 Core packet families

### A. Goal packet
Represents a theorem/search/research target.

Fields:
- `schema`
- `goal_key`
- `goal_kind`
- `entity_key`
- `canonical_shape`
- `target_pretty`
- `module`
- `imports`
- `lean_context`
- `representation_depth`
- `owner_candidate`
- `translator_candidates`
- `coherence_candidates`
- `priority`
- `created_at`
- `source`

### B. Retrieval packet
Produced by graph/Alexandria retrieval workers.

Fields:
- `schema`
- `retrieval_key`
- `goal_key`
- `retrieval_kind`: `graph` | `semantic` | `hybrid`
- `source_lane`: `arango8529` | `alexandria8530` | `jsonl_fallback`
- `freshness`
- `items`
- `scc_anchors`
- `raw_witnesses`
- `source_excerpts`
- `graph_outage`
- `stale_warning`
- `created_at`

### C. Proof-state packet
Produced only from Lean tooling.

Minimal JSON shape:
```json
{
  "schema": "hive.packet.proof_state.v1",
  "packet_key": "proofstate_...",
  "goal_key": "goal_...",
  "authority": "navigation",
  "representation_class": "owner",
  "representation_depth": "operatorial",
  "goal_text": "...",
  "proof_state": "...",
  "created_at": "..."
}
```

Fields:
- `schema`
- `proof_state_key`
- `goal_key`
- `imports`
- `context`
- `goal_text`
- `proof_state`
- `wrapper_version`
- `created_at`

### D. Proposal packet
Produced by a proposal bee.

Minimal JSON shape:
```json
{
  "schema": "hive.packet.proposal.v1",
  "packet_key": "proposal_...",
  "goal_key": "goal_...",
  "proof_state_key": "proofstate_...",
  "retrieval_key": "retrieval_...",
  "authority": "proposal",
  "representation_class": "owner",
  "representation_depth": "operatorial",
  "proposal_kind": "tactic",
  "content": "simp",
  "created_at": "..."
}
```

Fields:
- `schema`
- `proposal_key`
- `goal_key`
- `proof_state_key`
- `retrieval_key`
- `proposal_kind`: `tactic` | `theorem_snippet` | `bridge_lemma`
- `content`
- `rationale`
- `model`
- `created_at`

### E. Critique packet
Produced by critic/audit workers.

Minimal JSON shape:
```json
{
  "schema": "hive.packet.critique.v1",
  "packet_key": "critique_...",
  "proposal_key": "proposal_...",
  "authority": "proposal",
  "verdict": "approve",
  "reason": "...",
  "created_at": "..."
}
```

Fields:
- `schema`
- `critique_key`
- `proposal_key`
- `verdict`: `approve` | `revise` | `reject`
- `revised_content`
- `reason`
- `notes`
- `created_at`

### F. Execution-intent packet
Produced after critique has frozen the exact payload that may be sent to Lean or build tooling.

Minimal JSON shape:
```json
{
  "schema": "hive.packet.execution_intent.v1",
  "packet_key": "exec_...",
  "proposal_key": "proposal_...",
  "critique_key": "critique_...",
  "authority": "execution_intent",
  "intent_kind": "lean_tactic",
  "frozen_payload": {"tactic": "simp"},
  "created_at": "..."
}
```

Fields:
- `schema`
- `execution_intent_key`
- `proposal_key`
- `critique_key`
- `intent_kind`: `lean_tactic` | `lean_snippet` | `build_request`
- `frozen_payload`
- `created_at`

### G. Verification packet
Produced by execution workers.

Minimal JSON shape:
```json
{
  "schema": "hive.packet.verification.v1",
  "packet_key": "verify_...",
  "execution_intent_key": "exec_...",
  "authority": "lean_checked",
  "verification_kind": "lean_tactic",
  "status": "success",
  "created_at": "..."
}
```

Fields:
- `schema`
- `verification_key`
- `execution_intent_key`
- `verification_kind`: `lean_tactic` | `lean_snippet` | `build`
- `status`: `success` | `failure` | `environment_blocked`
- `stdout`
- `stderr`
- `latency_s`
- `created_at`

### H. Build packet
Produced only by the build authority path.

Minimal JSON shape:
```json
{
  "schema": "hive.packet.build.v1",
  "packet_key": "build_...",
  "verification_key": "verify_...",
  "authority": "build_checked",
  "resource_class": "lake_build",
  "state": "passed",
  "target": "InfoGeometry.Canonical.Operators",
  "created_at": "..."
}
```

Fields:
- `schema`
- `build_key`
- `verification_key`
- `resource_class`
- `state`: `lock_wait` | `running` | `passed` | `failed` | `environment_blocked`
- `target`
- `stdout`
- `stderr`
- `created_at`

### I. Audit packet
Produced by semantic/Pauli/promotion-audit workers.

Minimal JSON shape:
```json
{
  "schema": "hive.packet.audit.v1",
  "packet_key": "audit_...",
  "build_key": "build_...",
  "authority": "audit_checked",
  "verdict": "pass",
  "created_at": "..."
}
```

Fields:
- `schema`
- `audit_key`
- `build_key`
- `verdict`: `pass` | `conditional_pass` | `fail`
- `notes`
- `created_at`

### J. Fossil packet
Produced only after Lean-verified success.

Minimal JSON shape:
```json
{
  "schema": "hive.packet.fossil.v1",
  "packet_key": "fossil_...",
  "verification_key": "verify_...",
  "authority": "lean_checked",
  "const_name": "...",
  "created_at": "..."
}
```

Fields:
- `schema`
- `fossil_key`
- `goal_key`
- `verification_key`
- `const_name`
- `generated_source`
- `indexed_packet`
- `replay_packet_key`
- `created_at`

### K. Deadend packet
Produced after a truthful failed closure attempt.

A deadend packet may carry negative-antiproof metadata.  This does not claim
that the theorem is impossible; it certifies that a specific reduction path is
inadmissible or non-closing at a specific authority level.

Fields:
- `schema`
- `deadend_key`
- `antiproof_kind`: `proposal_rejection` | `lean_nonclosure` | `build_nonintegration` | `audit_nonpromotion` | `owner_shadow_conflict` | `synthetic_anchor_only` | `environment_blocked` | `missing_owner_theorem`
- `authority_level`: `proposal` | `lean_checked` | `build_checked` | `audit_checked`
- `corridor`
- `forbids_downstream`
- `global_impossibility_claim`
- `goal_key`
- `proposal_key`
- `verification_key`
- `failure_kind`
- `blocked_by_dependency`
- `retry_policy`
- `residue`
- `created_at`

Doctrine:
- fossils are positive expertise;
- deadends are negative expertise;
- replay is reusable success memory;
- negative antiproofs are reusable failure memory.

### L. Replay packet
Produced for every successful fossil and optionally for failed but instructive attempts.

Fields:
- `schema`
- `replay_key`
- `goal_key`
- `fossil_key`
- `proof_state_key`
- `retrieval_keys`
- `proposal_trace`
- `verification_trace`
- `artifact_paths`
- `created_at`

### M. Promotion-decision packet
Produced only after audit/build/fossil evidence has been reviewed by the promotion authority path.

Minimal JSON shape:
```json
{
  "schema": "hive.packet.promotion_decision.v1",
  "packet_key": "promote_...",
  "audit_key": "audit_...",
  "authority": "promoted",
  "decision": "promote",
  "created_at": "..."
}
```

Fields:
- `schema`
- `promotion_decision_key`
- `audit_key`
- `decision`: `promote` | `hold` | `reject`
- `reason`
- `created_at`

### N. TheoremCandidatePacket
The only legal bridge from Black Book / future-pass / research pressure into formal theorem work.

Minimal JSON shape:
```json
{
  "schema": "hive.packet.theorem_candidate.v1",
  "packet_key": "candidate_...",
  "authority": "semantic",
  "representation_class": "shadow",
  "representation_depth": "categorical",
  "formal_target": "...",
  "owner_surface": "...",
  "remaining_obligations": ["..."],
  "created_at": "..."
}
```

Fields:
- `schema`
- `candidate_key`
- `symbolic_origin`
- `formal_target`
- `owner_surface`
- `translator_surface`
- `coherence_surface`
- `bridge_claim`
- `novelty_defense`
- `current_anchors`
- `remaining_obligations`
- `graph_context_refs`
- `alexandria_context_refs`
- `promotion_ready`: yes/no
- `created_at`

## 5. Typed task model

A generic `hive_task` is too weak.

Greenfield the queue must carry explicit `task_kind`.

Every task and packet should also carry two orthogonal metadata fields:
- `authority`: `navigation` | `semantic` | `proposal` | `execution_intent` | `lean_checked` | `build_checked` | `audit_checked` | `promoted`
- `representation_class`: `owner` | `translator` | `coherence` | `capstone` | `shadow`

And, where applicable, an explicit `representation_depth`, for example:
- `scalar`
- `finite_matrix`
- `projective`
- `hilbert`
- `operatorial`
- `krein`
- `von_neumann`
- `type_iii`
- `categorical`

These fields are not decorative. They are the mechanism that prevents shadow packets from silently discharging owner obligations in this repository.

## 5.1 Required task kinds

Proof lane:
- `proof.search`
- `proof.retry`
- `proof.replay`
- `proof.promote`
- `proof.verify_snippet`
- `proof.fossilize`

Research lane:
- `research.fetch`
- `research.digest`
- `research.retrieve`
- `research.packetize`

Graph lane:
- `graph.retrieve`
- `graph.refresh`
- `graph.audit`

Audit lane:
- `audit.semantic`
- `audit.pauli`
- `audit.functorial`
- `audit.docstring`

Execution/resource lane:
- `build.verify`
- `build.strict`
- `build.locked`
- `artifact.compile_tex`

Doc lane:
- `doc.rewrite`
- `doc.docstring_distill`

## 5.2 Every task must declare
- `task_kind`
- `input_packet_refs`
- `required_capabilities`
- `resource_class`
- `retry_policy`
- `timeout_s`
- `priority`
- `queue_name`

## 6. Worker families

Before naming workers, the packet system should obey hard invariants.

## 6.1 Hard invariants

These are executable design rules, not merely prose aspirations.

1. `ResearchDigestPacket` cannot assert theorem closure.
2. `TheoremCandidatePacket` is formal intent, not proof evidence.
3. `VerificationPacket` cannot exist without an `ExecutionIntentPacket`.
4. `FossilPacket` cannot exist unless `VerificationPacket.status = success`.
5. `BuildPacket` is the only packet allowed to claim compilation success.
6. `PromotionDecisionPacket` is distinct from `BuildPacket` and `FossilPacket`.
7. A packet with `authority = navigation | semantic | proposal` cannot discharge theorem closure.
8. Shadow packets cannot discharge owner debts unless an explicit bridge morphism exists and that bridge is itself passed through the appropriate authority gates.
9. A worker may emit packets, but no worker may increase packet authority unless it belongs to an authority-gate family.

## 6.2 Worker families

The current swarm idea is good, but greenfield each family should be operationally simpler.

### 6.1 MotherBee / orchestrator
Capabilities:
- `schedule`
- `lease`
- `dependency_resolution`
- `resource_arbitration`
- `promotion_gate`

### 6.2 Retriever bee
Capabilities:
- `graph-retrieval`
- `raw-witness-descent`
- `alexandria-retrieval`

Output:
- retrieval packets only

### 6.3 Proof-state bee
Capabilities:
- `lean-proof-state`

Output:
- proof-state packets only

### 6.4 Proposal bee
Capabilities:
- `tactic-proposal`
- `theorem-snippet-proposal`

Output:
- proposal packets only

### 6.5 Critic bee
Capabilities:
- `proposal-critique`

Output:
- critique packets only

### 6.6 Lean executor bee
Capabilities:
- `lean-verification`
- `generated-snippet-check`

Output:
- verification packets only

### 6.7 Fossil bee
Capabilities:
- `fossilization`
- `hive_index_decl_capture`

Output:
- fossil + replay packets only

### 6.8 Research-digest bee
Capabilities:
- `arxiv-fetch`
- `alexandria-ingest`
- `semantic-retrieval`
- `packetization`

Output:
- research packets / theorem candidate packets

### 6.9 Audit bee
Capabilities:
- `pauli-audit`
- `semantic-audit`
- `promotion-audit`

Output:
- audit packets only

### 6.10 Build bee
Capabilities:
- `locked-build`
- `strict-build`
- `compile-tex`

Output:
- build verification packets only

## 7. State machines

## 7.1 Proof state machine

Transition table:

```text
proof.search:
  seeded
  -> retrieved
  -> proof_state_ready
  -> proposed
  -> critic_passed
  -> execution_intent_ready
  -> lean_checked
  -> build_checked
  -> audit_checked
  -> fossilized
  -> promotion_decided
```

Failure/side exits:

```text
retrieved            -> retrieval_blocked
proof_state_ready    -> environment_blocked
proposed             -> critic_reject
execution_intent_ready -> execution_blocked
lean_checked         -> deadend | requeued | semantic_blocked
build_checked        -> failed | environment_blocked | lock_wait
audit_checked        -> hold | reject
```

Canonical state vocabulary:
- `seeded`
- `retrieval_ready`
- `proof_state_ready`
- `proposed`
- `critic_passed`
- `execution_intent_ready`
- `lean_checked`
- `build_checked`
- `audit_checked`
- `fossilized`
- `promotion_decided`
- `deadend`
- `blocked`
- `requeued`

## 7.2 Research state machine
- `seeded`
- `fetched`
- `digested`
- `retrieved`
- `packetized`
- `ready_for_proof`
- `future_pass_only`

## 7.3 Build/resource state machine
- `queued`
- `lock_wait`
- `running`
- `passed`
- `failed`
- `environment_blocked`

This matters because the build lock should be visible as state, not inferred from logs.

## 8. Resource model

This is a major missing piece in the current architecture.

## 8.1 Resource classes
- `lean_exec`
- `lake_build`
- `graph_refresh`
- `alexandria_ingest`
- `proof_state_service`
- `fossil_index`
- `arango8529`
- `arango8530`
- `gpu_graph_rank`
- `doc_compile`

## 8.2 Build lock policy

Current repo memory already says to use:
- `tools/infra/run_locked_lake_build.py --wait-for-build-lock <Module>`

Greenfield this becomes a first-class resource queue policy:
- `build.locked` tasks enter the `lake_build` resource queue
- there is one lock-owning build worker or a bounded build pool
- lock owner, waiters, and start/finish timestamps are visible in Hive state
- stale terminal watch messages do not define truth; queue state does

## 9. Storage model

## 9.1 Event store
Append-only:
- worker heartbeats
- task claims/completions/failures
- audit events
- promotion events

## 9.2 Semantic packet graph
Mutable graph of current state:
- goals
- tasks
- fossils
- deadends
- retrieval packets
- replay packets
- candidate packets

## 9.3 Artifact filesystem
Append-only-ish local store:
- gravity packets
- Alexandria outputs
- proof-state logs
- generated theorem snippets
- build logs
- TeX compile outputs
- replay JSON

## 10. Promotion doctrine

The repository already strongly distinguishes:
- exploration
- theorem closure
- promotion

So greenfield:
- `verified` is not `promoted`
- `fossilized` is not `promoted`

Promotion requires:
1. Lean verification packet
2. fossil packet
3. semantic audit packet
4. Pauli audit packet
5. promotion decision packet

## 11. Failure taxonomy

Every failure should be semantically typed.

Required classes:
- `retrieval_unavailable`
- `retrieval_stale`
- `proof_state_failure`
- `proposal_empty`
- `critic_reject`
- `lean_tactic_failure`
- `generated_snippet_failure`
- `build_failure`
- `build_lock_wait`
- `dependency_fetch_failure`
- `environment_blocked`
- `missing_owner_theorem`
- `shadow_owner_confusion`
- `repo_state_divergence`

This is how the Hive learns real structure instead of just retrying blindly.

## 12. Observability and dashboards

At minimum, MotherBee should be able to answer:
- which workers are alive?
- what is queued by task kind?
- who holds the build lock?
- what is waiting on the build lock?
- what is blocked on graph outage?
- which theorem corridors are producing fossils?
- which deadends cluster around the same missing owner theorem?
- how much of the work is proof vs research vs audit vs build?

## 13. Greenfield collection suggestions

In addition to current collections, I would add:
- `hive_retrieval_packets`
- `hive_proof_state_packets`
- `hive_proposals`
- `hive_critiques`
- `hive_verifications`
- `hive_candidate_packets`
- `hive_promotions`
- `hive_resources`
- `hive_resource_leases`

And edges:
- `hive_goal_retrieved_by`
- `hive_goal_proposed_by`
- `hive_goal_verified_by`
- `hive_goal_promoted_by`
- `hive_packet_depends_on`
- `hive_task_consumes_packet`
- `hive_task_emits_packet`

## 14. Flow examples

## 14.1 Proof-search flow
1. `proof.search` goal seeded
2. MotherBee enqueues `graph.retrieve`
3. retriever bee emits graph retrieval packet
4. MotherBee enqueues `proof_state.prepare`
5. proof-state bee emits proof-state packet
6. MotherBee enqueues `proposal.generate`
7. proposal bee emits proposal packet
8. MotherBee enqueues `proposal.critique`
9. critic bee emits critique packet
10. if approved, MotherBee enqueues `proof.verify_snippet`
11. Lean executor emits verification packet
12. if successful, MotherBee enqueues `proof.fossilize`
13. fossil bee emits fossil + replay packets
14. MotherBee optionally enqueues `audit.semantic`
15. only then can a promotion decision exist

## 14.2 Research-digest flow
1. `research.digest` task seeded
2. fetch worker downloads sources
3. Alexandria ingest worker digests corpus
4. semantic retriever emits retrieval packet
5. packetizer emits `TheoremCandidatePacket`
6. MotherBee decides whether to enqueue proof tasks or leave as future-pass/research-only

## 14.3 Locked build flow
1. `build.locked` task seeded
2. build worker requests `lake_build` resource
3. if busy, task state becomes `lock_wait`
4. once acquired, state becomes `running`
5. run locked build
6. emit verification packet with status `passed` / `failed` / `environment_blocked`

## 15. Architectural rules derived from current repo memory and skills

These are not generic recommendations; they are specific to this repository.

1. Strong gravitation remains mandatory.
2. Lean REPL/proof-state wrapper remains the theorem firewall.
3. Alexandria remains semantic context, not theorem truth.
4. Replay packets must become first-class.
5. Residue/deadends must feed back into future work.
6. Build contention must become explicit queue state.
7. Shadow formulations must be marked as shadow in packet metadata.
8. Noncommutative operatorial ownerhood should inform task routing: scalar/finitary tasks must not silently outrank owner-lane obligations.

## 16. What I would implement first on a green field

1. typed task schema
2. retrieval packets as first-class outputs
3. build/resource leases in Hive state
4. separate proof-state / proposal / critic / executor workers
5. replay packet search before new model spend
6. theorem-candidate packet as the only bridge from Black Book/research to proof queue

## 17. Success condition

The Hive is successful when:
- every theorem claim has a Lean verification lineage,
- every research claim has an Alexandria/retrieval lineage,
- every build wait is visible as state,
- every deadend is reusable residue,
- every shadow remains visibly downstream of an owner lane,
- and MotherBee can explain the exact current state of the theorem factory without reading terminal noise.
