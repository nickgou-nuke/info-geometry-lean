# Hive Migration Plan (surgical, no rewrite)

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

## Current baseline
The repo already contains the core packetized Hive substrate:
- Arango queue + packet collections + indexes in `hive_arango_queue.py`
- Packet builders/validators in `hive_packet_build.py`, `hive_packet_validate.py`
- Worker split for build/audit/promotion and swarm orchestration

This plan hardens orchestration contracts without destabilizing active proof lanes.

## Phase 1 (now): runtime schema layer
- Add runtime schemas:
  - `tools/schema/hive_runtime/GoalPacket.schema.json`
  - `tools/schema/hive_runtime/AttemptPacket.schema.json`
  - `tools/schema/hive_runtime/GateReport.schema.json`
- Use them for queue ingress/egress API payloads and operator dashboards.

Acceptance:
- JSON schema validation passes for synthetic sample packets.
- No changes required to existing theorem packet builders.

## Phase 2: queue ingress hardening
- Update enqueue/claim code path to carry `goal_packet_key` and `attempt_packet_key` metadata.
- Keep backward compatibility with existing `hive_tasks` rows.

Acceptance:
- Existing workers still claim/complete tasks.
- New metadata appears for newly enqueued tasks.

## Phase 3: gate unification
- Emit GateReport after each verification/build/audit cycle.
- GateReport becomes canonical operator verdict for a run.

Acceptance:
- One GateReport can answer: Lean pass? Build pass? Audit pass? Promotion allowed?

## Phase 4: lease/resource visibility
- Normalize lock waiting under explicit `resource_wait_state` (`lock_wait`, `running`, `released`, `failed`).
- Surface through hive status command/report.

Acceptance:
- Operator can distinguish compute wait vs proof failure vs policy reject.

## Phase 5: policy reason-code hardening
- Standardize fail/reject reason codes across AuditPacket and PromotionDecisionPacket.
- Maintain string fields for compatibility but emit typed code arrays.

Acceptance:
- Promotion/reject is machine-queryable by reason code.

## What not to change yet
- Do not merge 8529 and 8530 DB lanes.
- Do not remove `run_locked_lake_build.py`.
- Do not demote Lean verification authority behind semantic retrieval.
- Do not collapse build/audit/promotion into one opaque worker again.

## Smoke tests after each phase
1. queue init: `python3 tools/infra/hive_arango_queue.py init`
2. packet validation: `python3 tools/infra/hive_packet_validate.py validate --packet <sample>`
3. synthetic flow:
   - enqueue synthetic goal
   - claim task
   - emit synthetic verification/build/audit packets
   - verify GateReport generation

## Deliverables produced in this change
- `docs/hive_greenfield_architecture.md`
- `tools/schema/hive_runtime/*.schema.json`
