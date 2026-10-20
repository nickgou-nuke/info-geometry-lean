# OpenGauss → Hive → Pi Collaboration Plan

## Purpose

Define a native, auditable path for transferring OpenGauss theorem work into
the repository Hive so Pi can collaborate without becoming a proof authority.

The transfer unit is a typed, provenance-bound packet. Free-form conversation,
provider output, and agent memory are navigation or proposal evidence only.
Lean and the locked repository checks remain the acceptance authority.

## Lane separation

The three persistence lanes must remain distinct:

| Lane | Repository interface | Role |
|---|---|---|
| AST/AQL declaration DAG | `ARANGO_ENDPOINT` / `ARANGO_DATABASE` | Owner declarations, dependency edges, AST/value/shape hashes |
| Hive queue | `HIVE_ARANGO_ENDPOINT` / `HIVE_ARANGO_DATABASE` | Goals, tasks, leases, worker heartbeats, packets, replay and audits |
| Agent memory | Explicit logical database such as `hive_memory` or `aiclaw_auto_rag` | Conversation/context retrieval; never proof authority |

The checked-out defaults are `8530/infogeometry` for the DAG and
`8540/hive_live` for the Hive queue. If a deployment exposes the DAG on port
`8030`, Pi must set `ARANGO_ENDPOINT` explicitly. It must not rewrite the Hive
queue or agent-memory defaults to make that mapping.

## OpenGauss intake contract

Before enqueueing, Pi must normalize an idea into a bounded theorem contract:

1. exact mathematical proposition;
2. actual carrier, operations, and scalar/ring assumptions;
3. owner Lean file and qualified declaration names;
4. source chunk IDs and immutable source hash;
5. imports and proved dependencies;
6. representation class and depth;
7. unsupported physical or metaphorical claims marked separately;
8. expected Lean target and verification command.

The contract must distinguish `theorem`, `conditional`, `evidence`, `conjecture`,
and `open_debt`. A graph match or model suggestion cannot be promoted to a
theorem contract without reading the owner source.

## Native Hive packet flow

Use `tools/infra/hive_arango_queue.py` and its packet validators. The causal
sequence is:

```text
theorem contract
  → hive.runtime.goal.v1
  → hive.packet.retrieval.v1
  → hive.packet.proof_state.v1
  → hive.packet.proposal.v1
  → hive.packet.critique.v1
  → hive.packet.execution_intent.v1
  → hive.packet.verification.v1
  → hive.packet.build.v1
  → hive.packet.audit.v1
  → hive.packet.promotion_decision.v1
```

Each packet must carry, where applicable:

```text
goal_key, task_key, lineage_id
source_hash, owner_file_hash, contract_hash
packet_sha256, parent_packet_keys
authority, representation_class, representation_depth
source_regime, worker_id, created_at
```

Use `import_packet_with_lineage` for packet insertion when dependencies must be
recorded. Use `enqueue-goal` only for the initial bounded task.

## Role separation

Pi may act as planner, normalizer, retriever, or proposal critic. Pi must not
write directly into Lean owners or emit `promoted` authority.

Recommended worker roles:

| Role | Output | Authority |
|---|---|---|
| Intake/Researcher | normalized contract and retrieval packet | `navigation` |
| Algebraist | symbolic witness or dependency notes | `proposal` |
| Formalist | Lean candidate in sandbox | proposal candidate |
| Lean verifier | kernel result | `lean_checked` |
| Build worker | serial locked build result | `build_checked` |
| Independent auditor | placeholder, vacuity, axiom and provenance audit | `audit_checked` |
| Promotion/QA worker | accept, hold, or reject decision | `promoted` only after all gates |

Producer, auditor, and promotion worker IDs must be distinct for a passing
promotion decision.

## Pi handoff packet

Pi should hand the Hive worker a JSON object containing:

```json
{
  "schema": "hive.packet.theorem_candidate.v1",
  "authority": "semantic",
  "source_regime": "normalized_intake",
  "representation_class": "native_mathlib",
  "representation_depth": "finite_algebraic",
  "formal_target": "exact Lean proposition",
  "owner_file": "lean/InfoGeometry/...lean",
  "owner_declarations": ["InfoGeometry.Namespace.owner"],
  "contract_hash": "sha256:...",
  "source_refs": ["chat-chunk-id", "document-id"],
  "asserts_theorem_closure": false
}
```

The candidate must remain sandbox-only until Lean verification and audit pass.

## Pantograph handoff boundary

Pantograph is the proof-session and exploration layer between a Hive proposal
and the Lean verifier. Pi may ask Pantograph to inspect the exact owner file,
reconstruct the proposition, or test candidate tactics. The handoff must bind
the session to:

- the contract hash;
- the owner-file hash and source snapshot;
- the qualified theorem name;
- the exact Lean proposition;
- the complete relevant compiler diagnostics.

Pantograph evidence is useful for navigation and repair, but it does not raise
packet authority. A successful provider response, tactic suggestion, or
Pantograph session is still only a candidate until the unchanged or explicitly
patched owner file passes `lake env lean`. The resulting Lean output, source
hash, and command line become the evidence for a `LeanVerificationPacket`, validated by
`tools/schema/hive/LeanVerificationPacket.schema.json`.

If the owner snapshot or contract hash changes, the Pantograph session is
stale and must be discarded or re-run. It must never write directly into a
Lean owner file or bypass the sandbox candidate path.

## Operational pilot

Run one finite task before enabling a swarm:

```bash
# Use an environment file that defines HIVE_ARANGO_* explicitly. Do not rely
# on generic ARANGO_* values for the Hive queue.
export HIVE_ARANGO_ENV_FILE=/path/to/hive-queue.env
./tools/infra/hive_with_env.sh init
./tools/infra/hive_with_env.sh status
./tools/infra/hive_with_env.sh queue-stats
./tools/infra/hive_with_env.sh enqueue-goal \
  --queue-name proof-search \
  --goal-hash-shape <shape-hash> \
  --canonical-shape <canonical-shape> \
  --target-pretty '<bounded theorem contract>' \
  --module InfoGeometry.Path.Owner \
  --goal-index 0
```

Then record:

- resolved DAG and Hive endpoints/databases;
- task key and packet SHA-256;
- worker heartbeat;
- atomic claim and lease expiry/requeue behavior;
- Lean result and exact command;
- locked build result where required;
- independent audit and QA result;
- final promotion decision or explicit rejection.

Do not claim that an empty queue or successful provider response proves Hive
operation. The pilot is complete only when the packet survives the full lineage
and verification path.

## Questions for Pi

1. Can Pi emit the complete theorem contract and source hashes without
   dropping provenance?
2. Which worker owns each transition in the packet sequence?
3. How will Pi distinguish navigation evidence from kernel evidence?
4. Where are sandbox candidates stored, and how are they prevented from
   overwriting owner files?
5. Which independent worker performs audit and QA?
6. How will Pi report unresolved claims instead of upgrading them to closure?
7. Does the deployment use the repository DAG default or an explicit `8030`
   `ARANGO_ENDPOINT` override?

## Acceptance criteria

The OpenGauss-to-Hive integration is accepted only when:

- packet schemas validate;
- source and owner hashes are recorded;
- DAG, Hive queue, and agent memory resolve to their intended lanes;
- leases and heartbeats are observable;
- Lean kernel evidence is captured;
- placeholder, vacuity, and axiom checks pass;
- build and audit packets are independently produced;
- no provider response is treated as proof;
- promotion is refused for incomplete, metaphor-only, or unsupported claims.

## Critical review and Socratic discussion

This plan is an architectural boundary, not yet an executable acceptance
contract. The following issues must be answered before the pilot is treated as
operational.

### Deployment boundary

The intended lanes are:

```text
AST/AQL DAG:  8530 / infogeometry
Hive queue:   8540 / hive_live
```

The Hive endpoint must be provisioned, authenticated, and schema-initialized
before a worker pilot. A reachable DAG endpoint does not establish that the
Hive queue is reachable. The launcher must fail closed when `HIVE_ARANGO_*` is
missing rather than silently routing Hive traffic to `ARANGO_*`.

### Schema authority

The conceptual packet names in this document must be mapped to the repository's
actual validator kinds and schema files. For example:

```text
LeanVerificationPacket  -> tools/schema/hive/LeanVerificationPacket.schema.json
AuditPacket              -> tools/schema/hive/AuditPacket.schema.json
PromotionDecisionPacket  -> tools/schema/hive/PromotionDecisionPacket.schema.json
```

The mapping must record the required fields, legal statuses, authority value,
and allowed predecessor packets. A prose name such as
`hive.packet.verification.v1` is not sufficient evidence of a valid packet.

### Contract-root requirement

`enqueue-goal` currently carries shape, target, module, and goal-index data, but
not the complete theorem contract. The system must decide whether a task can
exist without a validated `GroundTruthTheoremContract`. The recommended answer
is no: the contract packet is the immutable lineage root, and the goal/task
must reference its contract hash, owner declaration, owner-file hash,
non-claims, and required verification command.

### Hash protocol

Define one canonical protocol for:

- raw source bytes, encoding, and line endings;
- canonical JSON serialization;
- whether the packet hash excludes its own hash field;
- owner-file, candidate-snapshot, contract, and parent-packet hashes;
- pre- and post-execution source checks.

`packet_hash` and `packet_sha256` must not describe different algorithms or
canonicalization rules. Lean, build, audit, and promotion evidence must all
bind to the same byte snapshot.

### Independence and authority

Distinct worker IDs do not prove independent A-A or QA-A review. A passing
review must record distinct session IDs, origin-run IDs, input/context hashes,
and source snapshots. QA must not inherit the author's reasoning transcript.

Promotion must be monotone and reference-checked. The promotion worker must
reject missing or mismatched Lean verification, build, audit, source hashes,
placeholder/vacuity/axiom checks, or non-distinct review contexts. Provider
output must never be allowed to assert `promoted` authority by itself.

### Lease and crash semantics

The pilot must test each failure boundary:

```text
claim -> crash
claim + packet write -> crash
packet write + no completion -> crash
completion timeout
lease expiry
duplicate retry
```

The implementation must define at-least-once delivery, idempotent packet keys,
retry limits, terminal failure, orphan-packet reconciliation, and requeue
behavior that preserves the original packet without overwriting it.

### Sandbox and owner protection

Candidate paths must be allowlisted under a task-specific sandbox. The worker
must reject symlinks, traversal, owner-file writes, and source/hash changes
between intake, Lean checking, build, and audit. Integration is a separate
coordinator action after all gates; no worker or provider may edit an owner file
implicitly.

## Deep Socratic questions

1. What is the immutable root of lineage: contract, goal, or task?
2. Can any task be claimed before its theorem contract validates?
3. What exact bytes are hashed, and what canonicalization makes the hash
   reproducible across workers and hosts?
4. Which component is authorized to raise each authority level, and how is that
   restriction enforced by code rather than convention?
5. How is QA independence demonstrated rather than merely named?
6. What happens if the worker crashes after emitting a packet but before task
   completion, and how are duplicate emissions reconciled?
7. How does promotion prove that Lean, build, audit, and QA used the same
   source snapshot?
8. How are `not_executed`, `failed`, `rejected`, `deferred`, and `blocked`
   distinguished in the packet state machine?
9. Can Pi or any provider reach an owner-file write path directly?
10. How are DAG, Hive queue, and agent-memory credentials and databases
    prevented from crossing in a clean environment?
11. What is the exact bounded theorem target and qualified owner declaration
    for the first pilot?
12. What artifact proves that a requeued task preserves its original contract,
    candidate, and failure history?
13. What is the rollback policy for a promotion that later fails provenance
    or source-integrity review?
14. Which commands produce the decisive Lean, locked-build, axiom, vacuity,
    audit, and QA evidence, and where are their exact outputs stored?

The pilot is not accepted until these questions have file-backed answers and
those answers are checked against the repository-owned schemas and execution
paths.
