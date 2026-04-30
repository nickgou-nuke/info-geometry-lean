# Hive Greenfield Architecture (local-first, Lean-authoritative)

## Purpose
Build a packetized theorem-factory OS where:
- Lean kernel is truth authority.
- DAG is structural authority.
- Hive is execution/orchestration authority.
- Alexandria is semantic retrieval authority (never theorem truth).

## Hard boundaries
1. Lean closure is required for theorem truth.
2. Alexandria/research packets cannot promote theorem claims.
3. Promotion decision is separate from build success and separate from fossil creation.
4. DB split remains explicit:
   - 8529 theorem DAG and structural exports.
   - 8530 Hive queue/manifold + Alexandria semantic memory.

## Four planes

### 1) Truth Plane (Lean)
- Lean modules + Meta architecture checks.
- Strict admission commands and representation-depth checks.
- Token-free proof-state verification path via `tools/infra/lean_interact_wrapper.py`.

### 2) Structure Plane (DAG)
- `tools/infra/refresh_decl_graph.py` and managed wrappers (`dagRefresh`, `dagReports`, `dagAll`).
- Canonical artifacts under `artifacts/dag/`.
- Coverage, topology, and ownership reports under `reports/dag/`.

### 3) Epistemic Plane (Hive)
- Queue/task lifecycle + worker heartbeats + packet lineage in Arango.
- Packet families (already present): retrieval, proposal, critique, execution_intent, verification, build, audit, promotion_decision.
- Resource lease plane (`hive_resources`, `hive_resource_leases`) for lock-aware build visibility.

### 4) Semantic Plane (Alexandria)
- Chunk/entity/relation ingestion for research memory and context retrieval.
- Produces candidate/retrieval context, never Lean truth claims.

## Existing code reused directly
- `tools/infra/hive_arango_queue.py` (schema + queue + packet persistence + indexes)
- `tools/infra/hive_packet_build.py` (packet constructors)
- `tools/infra/hive_packet_validate.py` + `tools/schema/hive/*.schema.json`
- `tools/infra/hive_build_worker.py`, `hive_audit_worker.py`, `hive_promotion_worker.py`
- `tools/infra/run_locked_lake_build.py`

## Runtime contracts (new, execution-facing)
To stabilize orchestration boundaries, add three runtime packet contracts:
1. GoalPacket: theorem target intent contract.
2. AttemptPacket: one worker attempt with context/provenance.
3. GateReport: unified Lean/build/audit verdict payload.

These live in `tools/schema/hive_runtime/`.

## State machine
Goal state:
- queued -> claimed -> proposed -> execution_intent -> lean_checked -> build_checked -> audit_checked -> promoted
- failure branches emit residue/deadend packets with explicit reason codes.

Task state:
- queued -> claimed -> running -> completed|failed|timed_out|cancelled
- leases renewed via heartbeat; lock-wait represented explicitly in resource lease state.

## Promotion gate
Promotion requires all:
- LeanVerificationPacket: pass
- BuildPacket: success
- AuditPacket: pass (or explicit policy-approved warning profile)
- PromotionDecisionPacket: admitted

## Observability
- Append-only events in `hive_events`.
- Per-goal lineage query from candidate -> retrieval -> proposal -> execution_intent -> verification -> build -> audit -> promotion.
- No silent state transitions outside packet/event emission.

## Immediate adoption checklist
1. Keep current packet schemas and workers.
2. Introduce runtime Goal/Attempt/Gate contracts for orchestration UI and retries.
3. Enforce typed reason codes in promotion and failure paths.
4. Add CI smoke: packet validation + queue init + synthetic end-to-end gate path.
