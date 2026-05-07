# Hive Beehive Swarm Implementation Plan

> Status: `implementation plan`
> Authority: planning / architecture only; Lean, Lake, audit, and promotion gates remain authoritative.
> Scope: evolve the current Hive packet ledger into a practical Hermes-style beehive swarm.
> Related docs: `docs/hive_neural_backbone_architecture.md`, `docs/hive_greenfield_architecture.md`, `docs/hermes_recursive_hive_architecture.md`, `docs/HIVE_PACKET_JSON_SCHEMAS.md`, `docs/black_books/226_shadow_router_latent_space_splitting.md`.

## 0. One-sentence summary

The workable Hive is a typed theorem-factory nervous system: source intake and symbolic discovery create low-authority packets; bees transform those packets through Socratic, Pauli, retrieval, Lean, build, audit, and promotion gates; Arango records durable lineage; Hermes Swarm/Kanban provides the cockpit; Lean/Lake/Audit remain the truth authorities.

## 1. The real architecture, stripped of science fiction

The practical beehive has seven layers:

```text
1. Source and sensation layer
   papers, Black Books, web/search outputs, code scans, Lean declarations,
   proof states, compiler failures, old reports

2. Packet ledger
   schema-validated Hive packets with explicit authority, cognitive origin,
   source refs, owner refs, and admissible uses

3. Memory graph
   ArangoDB collections/edges for packets, sources, theorem owners, failures,
   motifs, complexes, routes, audits, and promotions

4. Worker bees
   small role-specific processes that consume tasks, emit packets, and never
   silently mutate authority

5. MotherBee router
   queue/scheduler that assigns packets to bees, detects stalled loops, records
   interrupts, and blocks invalid ascent

6. Formal authority descent
   TheoremCandidate -> ExecutionIntent -> LeanVerification -> Build -> Audit ->
   PromotionDecision

7. Hermes cockpit
   Kanban, Swarm sessions, reports, inbox, checkpoints, and operator review
```

The key separation:

```text
Hive generates pressure and lineage.
Bees transform packets.
Arango remembers structure.
Hermes coordinates work.
Lean decides theorem truth.
Lake decides build truth.
Pauli/Audit decide semantic hygiene.
Promotion admits or quarantines.
```

## 2. Non-negotiable authority law

The authority ladder remains unchanged:

```text
navigation
semantic
proposal
execution_intent
lean_checked
build_checked
audit_checked
promoted
```

Forbidden shortcuts:

```text
Symbolic motif -> proof
Dreamline -> execution
Complex interrupt -> promotion
Kanban done -> theorem admitted
Arango edge -> mathematical truth
Agent confidence -> LeanVerification
```

Required route for theorem-bearing work:

```text
source / motif / question / residue
  -> TheoremCandidatePacket
  -> ExecutionIntentPacket
  -> LeanVerificationPacket
  -> BuildPacket
  -> AuditPacket
  -> PromotionDecisionPacket
```

## 3. Beehive roles

### 3.1 MotherBee

MotherBee owns scheduling, not truth.

Responsibilities:

```text
- read queue state
- assign packets to bees
- enforce authority transitions
- detect repeated loops / complexes
- trigger Socrates and Pauli when needed
- enforce max attempts and cool-downs
- write routing decisions as packets or traces
```

Inputs:

```text
SourceObservationPacket
SymbolicMotifPacket
SocraticQuestionPacket
TheoremCandidatePacket
ExecutionIntentPacket
Lean/Build/Audit results
ComplexInterruptAuditPacket, future
```

Outputs:

```text
routing decision
bee task
interrupt record
quarantine decision
request for missing packet
```

### 3.2 SourceBee / SensationBee

Grounds the Hive in actual sources.

Responsibilities:

```text
- ingest Black Book chapters, papers, source files, Lean declarations
- create SourceObservationPacket
- attach source_ref and location data
- mark authority = navigation
- prevent source observations from becoming claims
```

### 3.3 RetrieverBee / MemoryBee

Finds relevant prior material.

Responsibilities:

```text
- query Arango and file corpus
- retrieve theorem owners, past attempts, deadends, Pauli critiques
- assemble evidence bundles
- compute route/failure similarity
- expose fossils without admitting them
```

### 3.4 SymbolicBee / IntuitionBee

Finds motifs and analogies.

Responsibilities:

```text
- create SymbolicMotifPacket
- relate Black Book motifs to current proof corridors
- propose analogies, not proofs
- attach allowed_uses and forbidden_uses
```

### 3.5 SocratesBee

Interrogates candidates.

Responsibilities:

```text
- create SocraticQuestionPacket
- ask what would falsify the candidate
- ask what definition is missing
- ask what weaker theorem would be exact
- route vague claims back to residue
```

### 3.6 PauliBee

Anti-inflation and owner/shadow separation.

Responsibilities:

```text
- create PauliCritique
- detect scalar-shadow overclaims
- detect missing owner theorem
- detect source/proof authority confusion
- quarantine inflated routes
```

### 3.7 BuilderBee / LeanBee

Formal descent into Lean.

Responsibilities:

```text
- consume ExecutionIntentPacket only
- run Lean/the repo wrapper on targeted modules
- emit LeanVerificationPacket
- record exact theorem, module, command, status, stderr/stdout digest
```

### 3.8 BuildBee

Compilation authority.

Responsibilities:

```text
- run locked Lake build or changedVerify surface
- emit BuildPacket
- never infer theorem truth beyond build result
```

### 3.9 AuditBee

Semantic authority check.

Responsibilities:

```text
- run Pauli/TSI/audit scripts or local audit model lane
- emit AuditPacket
- check overclaim, owner mismatch, symbolic inflation, stale docs
```

### 3.10 PromotionBee

Admission decision.

Responsibilities:

```text
- consume LeanVerificationPacket + BuildPacket + AuditPacket
- emit PromotionDecisionPacket
- admit / hold / quarantine
- write handoff evidence
```

### 3.11 ShadowBee / ExplorerBee

Sandboxed not-top exploration.

Responsibilities:

```text
- run only after MotherBee interrupt
- propose one orthogonal route
- emit SymbolicMotifPacket, SocraticQuestionPacket, FormulationVariant, or ResiduePacket
- never emit ExecutionIntentPacket directly
```

## 4. Evolutionary implementation plan

This plan deliberately starts boring. The beehive becomes intelligent only after
packet law, tests, and authority gates are stable.

## Phase 0 — Freeze doctrine and inventory current surfaces

Goal: make the current state explicit before adding machinery.

Tasks:

```text
0.1 Confirm current packet schemas under tools/schema/hive/.
0.2 Confirm validator registration in tools/infra/hive_packet_validate.py.
0.3 Confirm current queue and worker tools:
    tools/infra/hive_arango_queue.py
    tools/infra/hive_bee.py
    tools/infra/hive_swarm.py
    tools/infra/hive_packet_build.py
    tools/infra/hive_promotion_worker.py
    tools/infra/hive_audit_worker.py
    tools/infra/hive_build_worker.py
0.4 Confirm tests under tests/test_hive_*.py.
0.5 Produce a small architecture inventory report.
```

Verification:

```bash
.venv-py312/bin/python -m pytest \
  tests/test_hive_cognitive_packet_schemas.py \
  tests/test_hive_json_ingestor.py \
  tests/test_hive_arango_queue.py \
  tests/test_hive_swarm.py \
  tests/test_hive_bee.py -q
```

Expected:

```text
all selected Hive tests pass
```

## Phase 1 — Packet law foundation

Goal: all bees speak only schema-validated packet dialects.

Tasks:

```text
1.1 Add ComplexInterruptAuditPacket.schema.json.
1.2 Add RouteInvocationPacket.schema.json.
1.3 Add DreamlineExperimentPacket.schema.json.
1.4 Add ReweightDecisionPacket.schema.json.
1.5 Register them in hive_packet_validate.py.
1.6 Add tests that prove none can skip to execution/build/audit/promotion.
```

Acceptance criteria:

```text
- every new packet has authority fixed to navigation or semantic
- promotion_allowed = false where appropriate
- allowed_uses / forbidden_uses are required for dreamline/shadow packets
- validator rejects promoted authority on these packets
```

Verification:

```bash
.venv-py312/bin/python -m pytest tests/test_hive_cognitive_packet_schemas.py -q
python3 tools/infra/hive_packet_validate.py validate --packet /tmp/example_complex_interrupt.json
```

## Phase 2 — Local packet store before Arango dependence

Goal: allow development without a live database.

Tasks:

```text
2.1 Create a local JSONL packet append/read helper.
2.2 Add packet IDs and parent/child refs consistently.
2.3 Add a command to append a validated packet.
2.4 Add a command to list packets by kind/authority/complex_ref.
2.5 Add tests using tmp_path.
```

Suggested file:

```text
tools/infra/hive_local_packet_store.py
tests/test_hive_local_packet_store.py
```

Acceptance criteria:

```text
- append validates packet before writing
- invalid packet is rejected
- list/filter is deterministic
- no Arango required
```

## Phase 3 — Arango layered graph ingestion

Goal: make Arango a derived memory graph, not source authority.

Tasks:

```text
3.1 Map each packet kind to an Arango collection.
3.2 Add edges for parent_of, derived_from, critiques, verifies, builds, audits, promotes, blocks, resembles_complex.
3.3 Ingest packet JSONL into Arango idempotently.
3.4 Add projection/witness edges, never destructive rewrites.
3.5 Add tests with mocked/local Arango adapter where possible.
```

Suggested files:

```text
tools/infra/hive_arango_schema.py
tools/infra/hive_arango_ingest_packets.py
tests/test_hive_arango_packet_ingest.py
```

Acceptance criteria:

```text
- packet JSON remains canonical record
- Arango graph is rebuildable from packets
- graph edges carry source packet IDs
- no graph edge increases authority
```

## Phase 4 — Worker bee protocol

Goal: every bee has the same contract.

Bee contract:

```text
input: packet/task JSON
validate input
perform one bounded action
emit packet/report JSON
validate output
append output to store
return concise status
```

Tasks:

```text
4.1 Define BeeTask envelope.
4.2 Define BeeResult envelope.
4.3 Add base runner around tools/infra/hive_bee.py.
4.4 Add dry-run mode.
4.5 Add timeout and max-output guards.
4.6 Add tests for one fake bee.
```

Suggested files:

```text
tools/schema/hive/BeeTask.schema.json
tools/schema/hive/BeeResult.schema.json
tools/infra/hive_bee_runner.py
tests/test_hive_bee_runner.py
```

Acceptance criteria:

```text
- no bee can emit unvalidated packets
- every bee records input IDs and output IDs
- dry run produces no side effects
```

## Phase 5 — MotherBee scheduler v1

Goal: replace ad hoc orchestration with a small deterministic router.

Tasks:

```text
5.1 Define queue item states: pending, running, blocked, done, quarantined.
5.2 Define role routing table by packet kind.
5.3 Implement one-step scheduler: pop one packet, choose bee, enqueue task.
5.4 Add authority transition checks.
5.5 Add max retry counts.
5.6 Add tests for invalid transitions.
```

Suggested file:

```text
tools/infra/hive_motherbee_scheduler.py
tests/test_hive_motherbee_scheduler.py
```

Routing v1:

```text
SourceObservationPacket -> RetrieverBee / SymbolicBee
SymbolicMotifPacket -> SocratesBee / PauliBee
SocraticQuestionPacket -> RetrieverBee / ThinkingBee
TheoremCandidatePacket -> PauliBee / operator review
ExecutionIntentPacket -> LeanBee
LeanVerificationPacket -> BuildBee
BuildPacket -> AuditBee
AuditPacket -> PromotionBee
```

Acceptance criteria:

```text
- scheduler never routes semantic packets directly to LeanBee
- scheduler blocks invalid authority jumps
- scheduler writes a routing trace
```

## Phase 6 — Complex interrupt and not-top routing

Goal: make loop escape practical without making shadow authority.

Tasks:

```text
6.1 Compute proposal similarity across recent attempts.
6.2 Compute simple error fingerprint from Lean/compiler output.
6.3 Compute loop_information_gain from new sources/owners/hypotheses.
6.4 Implement exhaustion_score.
6.5 Emit ComplexInterruptAuditPacket when trigger fires.
6.6 Route one sandboxed Dreamline/Shadow task.
6.7 Force Pauli review before any execution intent.
```

Trigger:

```text
if consecutive_failed_lean_attempts >= 3
and proposal_self_similarity_norm >= 0.80
and loop_information_gain <= 1
and exhaustion_score >= 0.70:
  route_to_shadow_swarm = true
```

Acceptance criteria:

```text
- shadow route emits only pre-authority packets
- max_not_top_attempts_per_complex_per_day enforced
- require_sensation_source_contact_after_not_top enforced
- require_pauli_review_before_execution_intent enforced
```

## Phase 7 — Lean authority lane

Goal: formal work enters through explicit execution intent only.

Tasks:

```text
7.1 Define exact ExecutionIntent requirements for Lean action.
7.2 Use tools/infra/run_locked_lake_build.py for build-lock safety.
7.3 Integrate token-free Lean interact wrapper for proof-state checks when useful.
7.4 Emit LeanVerificationPacket with exact command, module, theorem, status.
7.5 Add regression tests around packet creation and failure capture.
```

Acceptance criteria:

```text
- no symbolic packet can call Lean directly
- failed Lean attempts become fossils/deadends
- successful Lean check still requires BuildPacket and AuditPacket
```

## Phase 8 — Build, audit, promotion lane

Goal: close the authority chain.

Tasks:

```text
8.1 BuildBee consumes LeanVerificationPacket.
8.2 BuildBee emits BuildPacket.
8.3 AuditBee consumes theorem + build evidence.
8.4 AuditBee emits AuditPacket.
8.5 PromotionBee consumes Lean + Build + Audit evidence.
8.6 PromotionBee emits PromotionDecisionPacket.
```

Acceptance criteria:

```text
- PromotionDecisionPacket requires evidence refs
- failed audit blocks promotion
- Kanban done is not accepted as promotion evidence
```

## Phase 9 — Hermes Swarm cockpit

Goal: make the beehive operable by humans and agents.

Tasks:

```text
9.1 Define Hermes role cards for MotherBee, SourceBee, RetrieverBee, SocratesBee, PauliBee, LeanBee, BuildBee, AuditBee, PromotionBee, ShadowBee.
9.2 Map Kanban columns to packet states, not theorem truth.
9.3 Add session report templates.
9.4 Add checkpoint rules: every major step links packet IDs and verification commands.
9.5 Add swarm launch script that starts only bounded local workers.
```

Acceptance criteria:

```text
- Hermes cockpit can show what is pending/running/blocked/done
- done means evidence handoff complete, not theorem admitted
- every dashboard card links to packet lineage
```

## Phase 10 — Evolutionary learning without hidden weight authority

Goal: let the Hive improve from experience without secret truth channels.

Tasks:

```text
10.1 Mine successful promotions for route patterns.
10.2 Mine quarantines for failure complexes.
10.3 Update retrieval weights and routing heuristics, not theorem authority.
10.4 Keep all learned policies as auditable ReweightDecisionPacket records.
10.5 Add periodic Pauli audit of routing policy drift.
```

Acceptance criteria:

```text
- learned routing policy is reproducible from records
- no hidden model memory becomes promotion authority
- operator can inspect why a route was preferred or penalized
```

## 5. Minimal viable beehive

The first useful swarm does not need all phases.

MVB = Minimal Viable Beehive:

```text
1. schema-validated packet ledger
2. local JSONL packet store
3. MotherBee scheduler v1
4. SourceBee / RetrieverBee / SocratesBee / PauliBee
5. LeanBee through ExecutionIntent only
6. BuildBee / AuditBee / PromotionBee skeletons
7. Hermes/Kanban cockpit mapping packet states
```

This is enough to run one theorem-corridor loop:

```text
SourceObservationPacket
  -> SymbolicMotifPacket
  -> SocraticQuestionPacket
  -> TheoremCandidatePacket
  -> PauliCritique
  -> ExecutionIntentPacket
  -> LeanVerificationPacket
  -> BuildPacket
  -> AuditPacket
  -> PromotionDecisionPacket
```

## 6. Recommended first implementation sequence

Do these in order:

```text
A. Add local JSONL packet store.
B. Add BeeTask/BeeResult envelopes.
C. Add MotherBee scheduler v1.
D. Add ComplexInterruptAuditPacket and RouteInvocationPacket.
E. Add simple route-similarity / loop-detection metrics.
F. Wire SourceBee, SocratesBee, PauliBee as packet-only workers.
G. Wire LeanBee behind ExecutionIntentPacket.
H. Wire BuildBee, AuditBee, PromotionBee.
I. Add Arango ingestion as a derived projection.
J. Add Hermes Swarm role cards and dashboard mapping.
```

Do not start with:

```text
- direct transformer KV-cache mutation
- autonomous Lean mutation loops
- Arango as source of truth
- dreamline-to-execution shortcuts
- model self-confidence as audit
```

## 7. One-line operating law

```text
The Hive evolves by remembering every source, question, failure, critique,
proof attempt, build result, audit, and promotion as typed packets; bees may
route and transform the packets, but only Lean/Lake/Audit/Promotion can raise
mathematical authority.
```
