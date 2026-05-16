# Hive Beehive Architecture (optimal, local-first, Lean-authoritative)

> Status: `reference memory`
> Audited: 2026-05-16
> Scope: the current optimal beehive architecture for `info-geometry-lean`
> Source docs read: `docs/hive_greenfield_architecture.md`, `docs/hive_migration_plan.md`, `docs/hive_graph_resident_os.md`, `docs/hermes_recursive_hive_architecture.md`, `docs/hive_neural_backbone_architecture.md`, `docs/hive_beehive_swarm_implementation_plan.md`
> Authority: design doctrine only; Lean, Lake, audit, and promotion gates remain authoritative for theorem claims.

## 0. Purpose

The beehive is a packetized theorem-factory operating system.
Its job is to turn raw pressure — sources, proof gaps, failed builds, theorem candidates, and symbolic motifs — into checked, lineaged, and reviewable work.

The optimal architecture is not “one agent with tools”. It is a swarm with hard authority boundaries:

- Hermes coordinates and persists work.
- Archon handles theorem/proof automation.
- Codex and Claude are specialist coding/review workers.
- Gemini is the long-context and fallback synthesis lane.
- Copilot is an alternate coding lane when its auth/quota path is healthy.
- OpenClaw is a control plane around Codex-style provider use.
- Pi is a lightweight provider lane.
- PaperClip is telemetry and verification evidence, not proof authority.
- Lean remains the truth authority.
- Lake/build remains the compilation authority.
- Audit/Pauli remain the semantic hygiene authority.

## 1. Design laws

1. Lean is the only authority for theorem truth.
2. Build success is not theorem truth.
3. Retrieval and semantic similarity are not theorem truth.
4. Agent confidence is not theorem truth.
5. Promotion is distinct from verification, build success, and fossilization.
6. Every claimed result must carry lineage: source -> packet -> worker -> verification -> decision.
7. Every long-running activity must be explicit state, not hidden in terminal noise.
8. Every fallback chain must be live-tested with the exact provider/model/auth triple before being trusted.
9. Every swarm role is disposable and replaceable; the ledger is durable.

## 2. Optimal swarm topology

Use five planes.

### 2.1 Control plane
Owns: orchestration, routing, claims, retries, scheduling, leases, and health.

Primary components:
- Hermes gateway / CLI / cron
- MotherBee / queue scheduler
- Kanban for durable asynchronous task state
- tmux or systemd user services for always-on workers

Responsibilities:
- accept incoming work
- choose worker lane
- emit tasks and packets
- renew leases
- detect stalls
- route retries and backoff
- record handoff state

### 2.2 Cognition plane
Owns: retrieval, candidate generation, critique, and synthesis.

Primary workers:
- Hermes + Gemini for broad synthesis and context expansion
- Claude for careful reasoning and review
- Copilot for alternate code-shaped generation
- Codex for implementation-shaped edits
- Archon for theorem/proof candidate generation

Responsibilities:
- search local files and graph memory
- produce theorem candidates
- generate critique and alternate formulations
- compress large context into taskable packets
- never declare truth

### 2.3 Execution plane
Owns: Lean, Lake, shell commands, build/test, proof-state verification.

Primary workers:
- Archon Lean lane
- Codex implementation lane
- local Lean wrappers and build scripts
- `run_locked_lake_build.py`

Responsibilities:
- run proof attempts
- run targeted builds/tests
- capture exact errors
- produce verification packets
- separate build failure from theorem failure

### 2.4 Storage plane
Owns: durable packet lineage and replay.

Primary stores:
- ArangoDB theorem DAG / topology memory
- Hive queue/runtime collections
- packet/event collections
- fossil/deadend residue collections
- repo artifact directories

Responsibilities:
- store every meaningful state transition
- keep immutable event history
- retain deadends as reusable memory
- keep the theorem DAG and Hive runtime state separate

### 2.5 Cockpit plane
Owns: human-facing control and observability.

Primary surfaces:
- Hermes CLI/gateway
- Kanban
- reports/inbox/checkpoints
- dashboards / status commands
- review surfaces for pauses, blocks, and promotion decisions

Responsibilities:
- let an operator see what the swarm is doing
- surface blocked work clearly
- present handoffs and evidence
- never hide proof authority behind UI state

## 3. Tool and role mapping

### Hermes
Use Hermes as the orchestrator and persistent control plane.

Best for:
- cron jobs
- multi-agent dispatch
- profile isolation
- memory
- gateway / always-on mode
- provider routing
- durable background jobs

### Archon
Use Archon for theorem/proof automation.

Best for:
- Lean proof search
- autoformalization loops
- proof corridor narrowing
- proof-target iteration

### Codex
Use Codex as the implementation worker.

Best for:
- file edits
- refactors
- batch fixes
- code review assistance
- branch/worktree-based tasks

### Claude
Use Claude as the reasoner/reviewer.

Best for:
- architecture review
- skeptical readthroughs
- refactor critique
- multi-step analysis
- consistency checking

### Gemini
Use Gemini as the broad synthesis / long-context lane.

Best for:
- summarizing large corpora
- expanding search space
- fallback routing
- proposal generation from long inputs

### Copilot
Use Copilot as an alternate coding agent when its auth/quota path is healthy.

Best for:
- code-shaped generation
- fallback coding lane
- GitHub-backed terminal workflows

### OpenClaw
Use OpenClaw as a Codex-oriented workflow shell when that control plane is useful.

Best for:
- Codex onboarding
- terminal workflow control
- provider switching around Codex-like lanes

### Pi
Use Pi as a lightweight provider lane.

Best for:
- cheap fallback
- simple worker tasks
- auxiliary generation when a lighter provider is enough

### PaperClip
Use PaperClip for telemetry and control evidence.

Best for:
- status records
- control outputs
- lane health evidence
- verification surfaces

Do not use PaperClip as a proof authority.

## 4. Current repo boundaries to keep explicit

The repo already has the right split in principle:

- `tools/infra/hive_arango_queue.py` — queue, claims, leases, events, packet persistence
- `tools/infra/hive_bee.py` — worker flow and task execution
- `tools/infra/hive_swarm.py` — swarm orchestration / role semantics
- `tools/infra/hive_build_worker.py` — build lane
- `tools/infra/hive_audit_worker.py` — audit lane
- `tools/infra/research_digest_worker.py` — research digestion lane
- `tools/infra/run_locked_lake_build.py` — explicit lock-aware build execution
- `tools/schema/hive/*.schema.json` — packet schema surface
- `tools/schema/hive_runtime/*.schema.json` — runtime goal/attempt/gate contracts

Architecture rule:
- keep Hive runtime state, theorem DAG state, and source artifacts as separate layers.

## 5. Packet model

The optimal beehive uses typed packets, not ad hoc notes.

Core packet families:
- SourceObservationPacket
- RetrievalPacket / RetrievalHypothesisPacket
- SymbolicMotifPacket
- SocraticQuestionPacket
- PauliCritique
- TheoremCandidatePacket
- ExecutionIntentPacket
- LeanVerificationPacket
- BuildPacket
- AuditPacket
- PromotionDecisionPacket
- ResiduePacket / DeadendPacket
- FossilPacket / ReplayPacket
- GoalPacket / AttemptPacket / GateReport for runtime control

Suggested authority ladder:

- navigation
- semantic
- proposal
- execution_intent
- lean_checked
- build_checked
- audit_checked
- promoted

Suggested metadata for every packet:
- authority
- authority_origin
- source_ref
- owner_ref
- representation_class
- representation_depth
- worker_role
- lane
- promotion_allowed

Hard rule:
- only the truth/builder/audit gates may raise authority.

## 6. Swarm execution loop

A healthy beehive loop is:

1. ingest source or task
2. classify the task
3. retrieve supporting context
4. generate one or more candidates
5. critique and shrink the candidate space
6. freeze an execution intent
7. run Lean/build/test
8. record verification
9. fossilize success or deadend failure
10. promote, hold, or quarantine

This means a swarm worker should never “just keep going” without emitting state.
Every meaningful transition must leave an artifact.

## 7. Continuous operation pattern

Use the right persistence primitive for the right job.

### For always-on control planes
Use:
- `systemd --user`
- Hermes gateway service mode
- Archon/OpenClaw servers

### For scheduled recurrent passes
Use:
- `hermes cron`
- queue-backed recurring jobs
- shell watchdog scripts when the output format is fixed

### For long interactive work
Use:
- `tmux`
- `terminal(background=true, notify_on_complete=true)`
- worktree-isolated workers

### For parallel code work
Use:
- git worktrees
- one worker per worktree
- one truth gate in the main repo

### For proof work
Use:
- one proof lane at a time for the final Lean truth gate
- background workers only as proposal engines
- verified build/test in the main repo

## 8. Optimal provider routing

The verified provider shape in this environment is:

- Hermes primary: `openrouter/free`
- Hermes fallback: `openai-codex gpt-5.4`
- Hermes lightweight fallback: `openai-codex gpt-5.4-mini`
- Hermes last resort: `gemini gemini-3-flash-preview`

Routing rules:
- verify the exact provider/model/auth triple before keeping it in the chain
- if a local fallback model is unreliable, make it configurable
- if Copilot is desired, verify the Copilot-specific auth path rather than assuming a plain GitHub token is enough
- Gemini API-key and Gemini CLI OAuth are separate paths; choose one explicitly

## 9. What “optimal” means here

The optimal architecture is the one that minimizes false authority and maximizes reusable evidence.

That means:
- one orchestrator
- many narrow workers
- explicit packets
- explicit leases
- explicit verification gates
- explicit fallback chains
- explicit deadends
- explicit promotion decisions

The swarm is successful when it can answer:
- what is the task?
- who owns it?
- what evidence exists?
- which gate passed?
- which gate blocked it?
- what can be retried?
- what is now durable memory?

## 10. Adoption checklist

1. Keep the old docs as historical background.
2. Treat this document as the current architecture target.
3. Keep Lean truth separate from Hive memory.
4. Keep Hermes as the cockpit, not the truth authority.
5. Keep build/promotion as separate gates.
6. Keep provider routing live-tested.
7. Keep every long-running worker visible in explicit state.
8. Prefer small, typed workers over a monolithic agent.

## 11. Summary

The beehive is best built as a four-plus-one system:

- control plane
- cognition plane
- execution plane
- storage plane
- cockpit plane

with Hermes coordinating, Archon proving, Codex/Claude/Gemini/Copilot supplying specialist cognition, and Lean/Lake/Audit deciding what survives.
