# Graph-Resident Hive Runtime Design

This document captures a runtime architecture where ArangoDB is the durable substrate and Lean remains the sole source of theorem truth.

## Core invariant

- Lean owns truth.
- Arango owns memory.
- The model owns proposals only.
- Bees are stateless and disposable.

## Runtime planes

1. **Lean truth plane**: Lean sources, Lake build, kernel checks, DAG exporters, audit/vacuity tooling.
2. **Graph substrate plane**: declaration + expression graph, topology overlays, motifs, and hole/Hodge metrics.
3. **Hive runtime plane**: goals/tasks/workers/resources plus immutable packet/event history.
4. **Bee worker plane**: specialized workers (retrieval, proposal, verification, audit, promotion, frontier, Hodge).
5. **Control plane**: leases, monitoring, replay, and scheduling feedback.

## Why this fits the existing repository

- `lean/DAG/README.md` already frames DAG outputs as navigation/audit under Lean truth.
- `lean/DAG/ExprArangoExport.lean` already emits Arango-style node/edge exports for declarations and expressions.
- `tools/infra/hive_arango_queue.py` already defines queue/task/event/lease and lineage primitives.
- `tools/infra/hive_bee.py` already follows retrieve → propose → Lean verify → fossil/deadend flow.

The implementation direction is therefore modularization and hardening, not wholesale rewrite.

## Data model

### Current-state collections

- `hive_goals`
- `hive_tasks`
- `hive_workers`
- `hive_resources`
- `hive_resource_leases`

### Immutable packet/event collections

- `hive_events`
- `hive_retrieval_packets`
- `hive_proof_state_packets`
- `hive_proposals`
- `hive_critiques`
- `hive_execution_intents`
- `hive_verifications`
- `hive_build_packets`
- `hive_audit_packets`
- `hive_candidate_packets`
- `hive_promotions`
- `hive_replay_packets`

### Memory/failure collections

- `hive_fossils`
- `hive_deadends`
- `hive_negative_constraints`
- `hive_sorry_obligations`

### Lineage collections

- `hive_task_for_goal`
- `hive_event_about`
- `hive_task_emits_packet`
- `hive_task_consumes_packet`
- `hive_packet_depends_on`
- `hive_goal_closed_by`
- `hive_goal_rejected_by`

## Authority levels

Enforce monotonic packet authority:

- `navigation`
- `semantic`
- `proposal`
- `execution_intent`
- `lean_checked`
- `build_checked`
- `audit_checked`
- `promoted`

Only verifier/build/audit/promotion workers can emit their corresponding elevated authorities.

## Worker split

- `MotherBee`: schedules tasks from goal impact + topology pressure.
- `RetrievalBee`: deterministic context packets from graph + fossils + negatives.
- `HydrationBee`: prompt-ready rendering, no model calls.
- `ProposalBee`: structured edits/proofs (JSON packets only).
- `CritiqueBee`: cheap policy gates before Lean.
- `VerifierBee`: Lean command execution and normalized failure recording.
- `AuditBee`: no-sorry/no-vacuity/layer policy checks.
- `PromotionBee`: success→fossil / failure→deadend+constraint.
- `FrontierBee`: Arango-native frontier scoring and enqueueing.
- `HodgeBee` and `GWHoleMetricBee`: derived geometric pressure metrics for scheduling.

## Queue and lease semantics

- Task claim is atomic and lease-based.
- Workers heartbeat in `hive_workers`.
- Work executes outside long transactions.
- Every meaningful state transition is reflected in immutable packets/events.

## Negative cache strategy

1. **Tactic-level** dedupe on `(state_before_hash, prompt_hash, patch_hash, failure_class)`.
2. **State-level** pruning on recurring dead-end goal-shape clusters.

Both should be consulted before expensive Lean invocations.

## Retrieval packet contract

Deterministically include:

1. Target declaration/signature/state hash.
2. SCC/topology placement and dominators.
3. Nearby support lemmas.
4. Shape-equivalent fossils.
5. Motif evidence.
6. Hole/Hodge pressure metrics.
7. Relevant negative constraints.
8. Namespace-density decision.

## Recommended package structure

```text
src/igf/hive/
  db.py
  schema.py
  queue.py
  packets.py
  retrieval.py
  hydration.py
  prompt.py
  model.py
  verifier.py
  audit.py
  negative_cache.py
  scheduler.py
  hodge_metrics.py
  gw_hole_metrics.py
  bees/
```

Keep existing scripts as wrappers while migrating internals.

## Minimal bring-up sequence

1. Export Lean declaration/expression graph.
2. Ingest into Arango (`ig_nodes`, `ig_edges`).
3. Build topology overlays.
4. Initialize hive queue/runtime collections.
5. Run one smoke-test bee.
6. Split specialized bees after end-to-end packet flow is verified.

## Smoke test expectations

For a canary target, verify:

1. Goal insertion.
2. Task creation/claim.
3. Retrieval packet write.
4. Proposal packet write.
5. Lean verification write.
6. Fossil or deadend emission.
7. Negative cache blocks duplicate failure attempts.

## Non-goals / guardrails

- No single monolithic orchestrator class.
- No model-selected dependencies outside retrieval envelope.
- No treating LSP diagnostics as theorem truth.
- No conflating graph metrics with kernel validity.
- No direct frontier mutation of source without verifier/audit/promotion chain.
- No removal of existing artifact workflows while introducing Arango-native runtime mode.

## One-line summary

A lease-driven, packet-emitting Hive where Arango is durable memory, Lean is truth authority, and every attempt—successful or failed—becomes reusable graph memory.
