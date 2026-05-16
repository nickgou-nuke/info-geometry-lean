# Hive Beehive Implementation Checklist

> Status: `reference memory`
> Audited: 2026-05-16
> Scope: map the optimal beehive architecture to the actual worker scripts and entrypoints
> Source docs read: `docs/hive_greenfield_architecture.md`, `docs/hive_migration_plan.md`, `docs/hive_graph_resident_os.md`, `docs/hermes_recursive_hive_architecture.md`, `docs/hive_neural_backbone_architecture.md`, `docs/hive_beehive_swarm_implementation_plan.md`
> Authority: planning and operator guidance only; Lean, Lake, audit, and promotion gates remain authoritative for theorem claims.

## 0. Purpose

This checklist translates the beehive architecture into concrete repo entrypoints.
Use it as the bridge between the doc-level architecture and the scripts that actually move packets, proofs, builds, and audits.

## 1. Canonical operating order

The healthy order is:

1. Initialize queue/runtime storage.
2. Bring up the control plane.
3. Route work into narrow workers.
4. Run retrieval / proposal / critique / proof / build / audit.
5. Record packets and lineage.
6. Promote only after the truth gates pass.

## 2. Control plane checklist

### 2.1 Initialize the Hive store

Use:
- `tools/infra/hive_arango_queue.py`

Typical purposes:
- create schema and indexes
- claim tasks
- track workers and leases
- record packet lineage
- persist goal/task state

Common checks:
- `python3 tools/infra/hive_arango_queue.py init`
- `python3 tools/infra/hive_ping.sh`
- `python3 tools/infra/hive_with_env.sh ...` when the queue needs env setup

### 2.2 MotherBee router

Use:
- `tools/infra/hive_motherbee.py`

What it does:
- reads validated packets from the local ledger
- applies deterministic routing rules
- appends BeeTask envelopes back into the ledger
- routes source observations, theorem candidates, and autoproof trace failures into narrower bees

Best use:
- dispatching from packet state to worker role
- deterministic scheduling / retry routing
- turning packet lineage into work items

### 2.3 Swarm orchestrator

Use:
- `tools/infra/hive_swarm.py`

What it does:
- runs generator / critic / auditor roles
- coordinates proposal generation
- keeps the human-facing swarm loop compact
- records run artifacts under `artifacts/hermes_loop/hive_swarm/`

Best use:
- local swarm sessions
- quick proposal→critic→audit loops
- operator-facing proof/analysis cycles

## 3. Proof lane checklist

### 3.1 Main proof worker

Use:
- `tools/infra/hive_bee.py`

What it does:
- claims tasks from the Hive queue
- retrieves graph-grounded context from Arango / gravity tools
- asks a prover model for a tactic
- verifies tactics through Lean interactively
- fossilizes success or records deadends

Best use:
- theorem-shaped work
- proof search
- proof-state driven tactic attempts

### 3.2 Specialized proof workers

Use:
- `tools/infra/hive_leanstral_bee_worker.py`
- `tools/infra/hive_leansearch_bee.py`
- `tools/infra/hive_loogle_bee_worker.py`
- `tools/infra/hive_bee_runner.py`
- `tools/infra/hive_packet_path_runner.py`

What they do:
- specialize retrieval and proof-proposal behavior
- target particular proof lanes or search backends
- support narrower theorem corridors and packet-path workflows

Best use:
- when the generic proof bee is too broad
- when a corridor needs proof-search specialization
- when you want a repeatable local proof session around one target

## 4. Build lane checklist

### 4.1 Locked build worker

Use:
- `tools/infra/hive_build_worker.py`
- `tools/infra/run_locked_lake_build.py`

What it does:
- claims `build.verify` tasks
- emits explicit `lock_wait`, `running`, and final build packets
- runs Lake only through the locked wrapper
- keeps build waiting visible instead of implicit

Best use:
- repository build truth
- long-running build/verify jobs
- explicit build-lock visibility

### 4.2 Higher-level build orchestration

Use:
- `tools/infra/dgx_spark_hybrid_orchestrator.py`
- `tools/infra/run_full_dag_toolchain.py`
- `tools/infra/build.py`

What they do:
- orchestrate larger build surfaces
- drive DAG/report refresh chains
- coordinate broader build toolchains around the locked build wrapper

Best use:
- umbrella refreshes
- staged DAG/build runs
- higher-level build scheduling

## 5. Audit lane checklist

### 5.1 Semantic audit worker

Use:
- `tools/infra/hive_audit_worker.py`

What it does:
- consumes build packets
- checks the referenced verification packet
- inspects upstream provenance
- emits `AuditPacket`
- refuses to become promotion authority

Best use:
- overclaim detection
- proof/build hygiene
- build-to-audit separation

### 5.2 Policy and multichecker surfaces

Use:
- `tools/infra/hive_spec_submission_policy.py`
- `tools/infra/hive_workflow_policy.py`
- `tools/infra/hive_multichecker_merge.py`

What they do:
- encode submission policy
- enforce workflow policy
- merge or validate multiple checker outputs

Best use:
- gatekeeping around promotion
- policy validation
- audit hardening

## 6. Research lane checklist

### 6.1 Research digestion worker

Use:
- `tools/infra/research_digest_worker.py`

What it does:
- ingests research material into Alexandria / Arango-backed memory
- fetches and digests context
- writes event and lineage records
- keeps the research lane separate from theorem truth

Best use:
- source ingestion
- arXiv / corpus digestion
- context retrieval before theorem work

### 6.2 Predigestion and demo surfaces

Use:
- `tools/infra/hive_predigestion_ingest.py`
- `tools/infra/run_predigestion_to_hive_demo.py`

What they do:
- stage upstream material into Hive-ready packets
- demonstrate the ingestion pipeline end to end

Best use:
- intake testing
- demo or smoke runs
- feedstock conversion before swarm dispatch

## 7. Packet storage and validation checklist

Use:
- `tools/infra/hive_local_packet_store.py`
- `tools/infra/hive_packet_build.py`
- `tools/infra/hive_packet_validate.py`
- `tools/infra/ingest_hive_json.py`

What they do:
- persist packets locally
- construct schema-compliant packets
- validate packet shape
- ingest JSON payloads into the Hive ledger

Best use:
- packet generation
- schema validation
- local ledger reproduction
- debugging packet lineage

## 8. Continuous operation checklist

### 8.1 Always-on workers

Use one of:
- `systemd --user`
- `tmux`
- Hermes gateway / cron
- `terminal(background=true, notify_on_complete=true)` for bounded long jobs

Recommended always-on lanes:
- `hive_motherbee.py`
- `hive_swarm.py`
- `hive_bee.py`
- `hive_build_worker.py`
- `hive_audit_worker.py`
- `research_digest_worker.py`

### 8.2 Recurring checks

Use:
- `hermes cron`
- queue-driven polling loops
- explicit health probes such as `hive_ping.sh`

Recommended recurring jobs:
- queue health
- build-lock health
- proof-lane health
- audit backlog sweeps
- research ingestion sweeps

### 8.3 Parallel workers

Use:
- git worktrees for code edits
- one worker per worktree
- one build truth gate in the main repo

Best fit:
- Codex for edits
- Claude for review
- Gemini for synthesis
- Archon for proof attempts

## 9. Recommended default deployment shape

A sensible minimal deployment is:

- Hermes: the orchestrator
- MotherBee: packet router
- Swarm: human-facing worker loop
- Bee: proof/search lane
- BuildBee: build truth lane
- AuditBee: semantic gate
- ResearchDigestWorker: intake lane
- Packet store + queue: durability layer

That gives you a complete loop without collapsing responsibilities.

## 10. Smoke-test sequence

Run these in order after wiring or doc changes:

1. `python3 tools/infra/hive_arango_queue.py init`
2. `python3 tools/infra/hive_ping.sh`
3. run a synthetic packet/goal through MotherBee
4. run one proof-lane task through `hive_bee.py`
5. run one build-lane task through `hive_build_worker.py`
6. run one audit-lane task through `hive_audit_worker.py`
7. confirm lineage records exist for the run

## 11. What not to do

- Do not collapse proof, build, audit, and promotion into one opaque worker.
- Do not treat retrieval or semantic similarity as truth authority.
- Do not hide build waits or task leases in silent process state.
- Do not let PaperClip-style telemetry become mathematical authority.
- Do not assume a provider route works until it has been live-tested.

## 12. Summary

This checklist is the operational bridge from architecture to scripts.
The key rule is simple:

- Hermes coordinates,
- MotherBee routes,
- workers stay narrow,
- Lean decides truth,
- Lake decides build truth,
- Audit decides hygiene,
- and lineage records everything.
