# Hive Formal Superorganism Architecture v0.1

Status: doctrine draft / policy surface
Scope: Hive, Paperclip, open-multi-agent, OpenClaw, Hermes/MotherBee, WorkerBees, packet ledger, Arango projection, Lean/Lake/build/audit/promotion authority chain

## Core doctrine

The Hive is a formal superorganism.

It may use swarm intelligence, autonomic regulation, reflex decomposition, graph topology, quorum pressure, debate, critique, and external limbs.

But mathematical authority is not emergent.

Mathematical authority changes only through typed authority packets emitted by the proper authority organs under MotherBee packet-law constraints.

```text
Control may change scheduling pressure.
Evidence may change search state.
Authority packets may change accepted mathematical state.
```

Hard invariant:

```text
No metaphor, dashboard, graph path, quorum, consensus, confidence score,
agent synthesis, or control signal may increase mathematical authority.

Emergence guides search; authority remains typed, local, checkable, and
lineage-preserving.
```

## Superorganism mapping

```text
Human / operator / board
  reflective override, explicit approvals, strategic direction

Paperclip
  autonomic/endocrine regulation: backlog pressure, wake/cooldown, budgets,
  heartbeats, load balancing, blockers, review demand
  ceiling: control

open-multi-agent / DAGCompilerBee
  replaceable reflex ganglion: goal -> proposed task DAG
  ceiling: task proposal

OpenClaw
  peripheral limbs and sensors: chat, browser, external applications,
  notifications, approval relay
  ceiling: external I/O

Hermes / MotherBee
  regulatory legality integrator: admits/rejects motion, enforces packet law,
  role policy, authority ceilings, and required lineage

WorkerBees
  bounded organs/cells: role-specific packet transformations under BeeTask
  contracts

JSONL packet ledger
  durable metabolic memory and repair lineage
  ceiling: lineage, not proof by itself

Arango
  derived neural/topological manifold: retrieval, SCC/module topology,
  semantic overlays, negative constraints, lineage exploration
  ceiling: derived navigation

PauliBee / AuditBee
  immune and diagnostic membranes: block, quarantine, hold, critique, audit
  hygiene

Lean / Lake / build
  mechanical spine / kernel truth boundary: typechecking and build stability

PromotionBee
  admission organ: accepted-memory transition only after required authority
  lineage
```

## Three packet classes

### 1. Control packets

Control packets change routing, wakefulness, priority, budget, cooldown, blocker state, or review demand.

They do not change mathematical authority.

Examples:

```text
BacklogPressureSignal
WorkerLoadSnapshot
WakeSignal
CooldownSignal
RouteRequest
PriorityAdjustment
BudgetEnvelope
BudgetThrottlePacket
HeartbeatSchedule
BlockerSignal
HumanApprovalRequest
ReviewEscalationSignal
StallRecoverySignal
RouteAdmissionDecision
ReweightDecisionPacket
QuarantineSignal
ConsolidationSchedule
TaskDAGProposalPacket
DAGNodeAdmissionDecision
```

Canonical control packet shape:

```json
{
  "packet_id": "pkt_...",
  "kind": "BacklogPressureSignal",
  "authority_class": "control",
  "may_change_authority": false,
  "promotion_allowed": false,
  "requires_motherbee_admission": true
}
```

### 2. Evidence / domain packets

Evidence/domain packets change mathematical or search lineage, but not final authority.

Examples:

```text
SourceObservationPacket
SymbolicSeed
FormulationVariant
ResonanceCluster
SocraticQuestionPacket
TheoremCandidatePacket
TranslationPacket
RetrievalHypothesisPacket
ProposalPacket
PauliCritique
NegativeConstraintPacket
DeadendPacket
ResiduePacket
ExecutionIntentPacket
```

`PauliCritique` is immune/diagnostic evidence. It may block, lower confidence, require reformulation, or quarantine a corridor. It does not prove.

### 3. Authority packets

Authority packets change authority state only if emitted by the proper authority organ and backed by required evidence.

Examples:

```text
LeanVerificationPacket
BuildPacket
AuditPacket
PromotionDecisionPacket
```

Canonical authority packet shape:

```json
{
  "packet_id": "pkt_...",
  "kind": "LeanVerificationPacket",
  "authority_class": "authority",
  "authority_level": "lean_checked",
  "emitter": "LeanBee",
  "evidence_ref": "artifact://lean-log/...",
  "requires": ["ExecutionIntentPacket"]
}
```

## Authority ladder

```text
navigation
  -> semantic
  -> proposal
  -> execution_intent
  -> lean_checked
  -> build_checked
  -> audit_checked
  -> promoted
```

The theorem route is:

```text
source/research/symbolic pressure
  -> TheoremCandidatePacket
  -> optional/required critique lane:
       PauliCritique | SocraticQuestionPacket | NegativeConstraintPacket
  -> ExecutionIntentPacket
  -> LeanVerificationPacket
  -> BuildPacket
  -> AuditPacket
  -> PromotionDecisionPacket
```

The critique lane may be mandatory by policy for selected theorem corridors, but critique is not theorem authority.

## Authority organ map

```text
LeanVerificationPacket:
  allowed emitter: LeanBee
  required input: ExecutionIntentPacket
  required evidence: Lean/Lake check log or equivalent local proof evidence
  meaning: a Lean artifact typechecks under the locked environment

BuildPacket:
  allowed emitter: BuildBee
  required input: LeanVerificationPacket
  required evidence: locked Lake/build log
  meaning: the repository/build state stabilizes

AuditPacket:
  allowed emitter: AuditBee
  required input: BuildPacket
  required evidence: audit report
  meaning: the claim, lineage, owner/shadow relation, synthetic status, and
  evidence story are honest enough for promotion review, hold, or rejection

PromotionDecisionPacket:
  allowed emitter: PromotionBee
  required input: AuditPacket
  required evidence: promotion policy evaluation
  meaning: accepted-memory admission, hold, or rejection
```

Lean is the type-theoretic truth boundary. Audit is the semantic/provenance hygiene boundary. Promotion is accepted repo-memory admission.

## Control organ map

```text
BacklogPressureSignal:
  allowed emitter: PaperclipAutonomicBridge

WorkerLoadSnapshot:
  allowed emitter: PaperclipAutonomicBridge, MotherBee, worker monitor

WakeSignal:
  allowed emitter: PaperclipAutonomicBridge or MotherBee

RouteRequest:
  allowed emitter: PaperclipAutonomicBridge, operator, or MotherBee

RouteAdmissionDecision:
  allowed emitter: MotherBee only

TaskDAGProposalPacket:
  allowed emitter: DAGCompilerBee / open-multi-agent

DAGNodeAdmissionDecision:
  allowed emitter: MotherBee only
```

All non-authority systems are authority-negative by default:

```text
Paperclip: promotion_allowed=false
open-multi-agent: promotion_allowed=false
OpenClaw: promotion_allowed=false
CrewAI/AG2/LangGraph/OpenAI Agents SDK worker lanes: promotion_allowed=false
Arango projection: promotion_allowed=false
```

## Paperclip boundary

Paperclip is the Hive's autonomic/endocrine control plane.

It observes:

```text
proof backlog
stale tasks
worker load
budget burn
blocked corridors
negative-constraint density
build-lock contention
human-review backlog
heartbeat freshness
```

It may:

```text
create operator-visible issues
show packet refs and lineage roots
show build/audit logs
wake workers
throttle budgets
request review
surface blockers
rebalance load
emit control packets
```

It may not:

```text
raise packet authority
emit LeanVerificationPacket, BuildPacket, AuditPacket, or PromotionDecisionPacket
decide theorem truth
treat issue done as proof done
bypass MotherBee
mutate the proof ledger directly
```

Canonical invariant:

```text
Paperclip status is operational status.
Hive packet status is domain-lineage status.
Lean/build/audit/promotion status is authority status.

No Paperclip transition may imply a stronger Hive authority transition.
```

## open-multi-agent boundary

`open-multi-agent` is a replaceable DAGCompilerBee / reflex ganglion. It is not durable memory and not authority.

Its default mode is:

```text
mode: planOnly
tools: none or read-only
repo_write: false
bash: false
hosted_provider: false unless explicitly allowlisted
output: TaskDAGProposalPacket only
authority_ceiling: navigation
```

Boundary invariants:

```text
OMA DAG node != Hive BeeTask.
OMA task completion != theorem completion.
OMA synthesis != promoted result.
OMA memory != Hive ledger.
OMA dashboard != authority trace.
```

MotherBee typechecks OMA's proposed DAG. Only accepted nodes become BeeTasks.

## OpenClaw boundary

OpenClaw is a peripheral sensor/limb gateway.

It may:

```text
notify humans
receive approvals
send status updates
perform external observational tasks
operate chat/browser/external application surfaces under explicit envelope
```

It may not:

```text
decide truth
promote packets
bypass MotherBee
perform proof authority transitions
```

## MotherBee validation law

MotherBee rejects any packet/task/path that violates authority ceilings or required lineage.

Hard validation for authority packets:

```text
if packet.authority_class == "authority":
    require emitter in authority_organs_for_kind[kind]
    require all required input packet kinds present
    require evidence_ref present
    reject if source.system == "paperclip"
    reject if source.system == "open-multi-agent"
    reject if source.system == "openclaw"
```

Additional rejects:

```text
Reject if assigned_role is incompatible with task_kind.
Reject if allowed_output_kinds exceeds authority_ceiling.
Reject if repo write is requested without ExecutionIntentPacket.
Reject if theorem/audit/promotion language appears in a Paperclip-only terminal state.
Reject if packet lineage root is missing for non-observer domain work.
Reject if build/audit/promotion gates are bypassed.
Reject if Arango path, quorum, consensus, dashboard done, or model confidence is used as authority evidence.
```

## BeeTask / BeeResult law

`BeeTask` is an ephemeral dispatch instruction, not knowledge and not authority.

It must carry at least:

```text
task_kind
assigned_role
objective
authority_ceiling
allowed_output_kinds
forbidden_output_kinds
limits
source refs
lineage refs when domain work is non-observer
```

`BeeResult` is a compute receipt, not authority.

It records:

```text
what ran
what inputs were consumed
what packets were emitted
what artifacts were written
what failed
what should happen next
```

Default:

```text
BeeResult.promotion_allowed = false
```

## Durable memory and graph projection

The durable memory is the append-only JSONL packet ledger.

It records:

```text
packet id
lineage id
input refs
output refs
authority class and authority level
representation class
representation depth
source
timestamp
artifact refs
validation result
```

Arango is a rebuildable derived projection:

```text
packet lineage graph
retrieval graph
theorem DAG overlay
SCC/module topology
semantic overlays
deadend/negative-constraint overlays
worker/load projections
```

Hard rule:

```text
If Arango is lost, lineage survives in JSONL.
If JSONL/Lean evidence is absent, Arango cannot create authority.
```

## Quorum, debate, and biological signals

Quorum, debate, and biological/autonomic signals may change routing confidence or scheduling pressure. They may not prove.

Examples:

```text
three independent agents agree a route is promising
  -> may increase priority or request a LeanBee attempt

three independent critics flag owner/shadow drift
  -> may route to PauliBee or cooldown

three similar Lean failures
  -> may emit NegativeConstraintPacket or route to SocratesBee
```

But:

```text
three agents agree theorem is true
  != theorem true
```

Only Lean/build/audit/promotion can move authority.

## Graph lambda / Arango proof search boundary

Graph search may propose candidate morphisms or proof paths. It may not admit them.

Correct route:

```text
Graph candidate path
  -> ProposalPacket
  -> optional/required critique lane
  -> ExecutionIntentPacket
  -> LeanBee runs actual Lean check
  -> LeanVerificationPacket if accepted by Lean
  -> BuildPacket
  -> AuditPacket
  -> PromotionDecisionPacket
```

Arango stores navigation and lineage projections. Lean remains authority.

## First implementation slices

### Slice 0: Observer + control packets

Goal: make Paperclip visible but non-authoritative.

Implement:

```text
BacklogPressureSignal
WorkerLoadSnapshot
RouteRequest
RouteAdmissionDecision
BeeTask
BeeResult
```

Do not implement yet:

```text
autonomous repo write
OMA execution
promotion bridge
hosted provider execution
direct Arango mutation from Paperclip
```

Acceptance tests:

```text
1. Paperclip can create BacklogPressureSignal.
2. MotherBee can admit or reject RouteRequest.
3. Rejected RouteRequest does not create BeeTask.
4. Admitted RouteRequest creates BeeTask with explicit authority_ceiling.
5. Paperclip issue status "done" does not create PromotionDecisionPacket.
6. Paperclip cannot emit LeanVerificationPacket, BuildPacket, AuditPacket, or PromotionDecisionPacket.
7. BeeResult defaults to promotion_allowed=false.
8. Arango projection can be rebuilt from JSONL.
```

### Slice 1: OMA planOnly DAGCompilerBee

Goal: use OMA only as decomposition organ.

Implement:

```text
TaskDAGProposalPacket
DAGNodeAdmissionDecision
MotherBee DAG node validation
```

Policy:

```text
OMA mode = planOnly
tools = none or read-only
repo_write = false
bash = false
hosted_provider = false unless explicitly allowlisted
output = TaskDAGProposalPacket only
```

Acceptance tests:

```text
1. OMA DAG node is not executable until MotherBee admits it.
2. DAG node requesting authority packet is rejected.
3. DAG node requesting repo write without ExecutionIntentPacket is rejected.
4. Legal RetrieverBee node becomes BeeTask.
5. Legal PauliBee node becomes BeeTask.
6. OMA final synthesis cannot mark theorem as proved.
```

### Slice 2: Authority ladder enforcement

Goal: prevent all theorem-promotion shortcuts.

Implement:

```text
ExecutionIntentPacket
LeanVerificationPacket
BuildPacket
AuditPacket
PromotionDecisionPacket
```

Validation:

```text
each authority packet requires exact predecessor packet type
each authority packet requires proper emitter
each authority packet requires artifact/evidence reference
```

Acceptance tests:

```text
1. LeanVerificationPacket without ExecutionIntentPacket is rejected.
2. BuildPacket without LeanVerificationPacket is rejected.
3. AuditPacket without BuildPacket is rejected.
4. PromotionDecisionPacket without AuditPacket is rejected.
5. PromotionDecisionPacket from Paperclip/OMA/OpenClaw is rejected.
6. PromotionDecisionPacket decision=promote is impossible on synthetic/smoke-only lineage.
```

## Suggested implementation layout

```text
hive/
  doctrine/
    ARCHITECTURE.md
    AUTHORITY_LADDER.md
    BIOLOGICAL_MAPPING.md

  schemas/
    packets/
      control/
      domain/
      authority/
    runtime/

  motherbee/
    validate_packet.py
    validate_beetask.py
    validate_dag_proposal.py
    authority_ladder.py
    role_policy.py
    admission.py

  bridges/
    paperclip_autonomic_bridge/
    oma_dagcompiler_bridge/
    openclaw_gateway_bridge/

  ledger/
    append_packet.py
    read_lineage.py
    replay_jsonl.py
    project_to_arango.py

  arango_projection/
    schema.py
    build_projection.py
    queries/
```

This layout is a future implementation target. Current repo paths may differ; implementation must be grounded in current code before promotion.

## Compact doctrine

```text
The Hive is a formal superorganism, not a swarm democracy.

Paperclip may regulate effort.
OMA may propose decomposition.
OpenClaw may sense and act.
WorkerBees may transform packets.
Arango may reveal topology.
Quorum may raise routing confidence.
Pauli/Audit may reject infection.
Lean/build may supply mechanical evidence.
PromotionBee may admit only after required lineage.

No metaphor, dashboard, graph path, quorum, consensus, confidence score,
agent synthesis, or control signal may increase mathematical authority.
```

One-line invariant:

```text
Emergence guides search; authority remains typed, local, checkable, and lineage-preserving.
```
