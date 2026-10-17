# Hive runtime-instance lineage: candidate design

Status: G-A proposal only. This document is not an implementation, audit, or
acceptance record. No existing source file was modified for this proposal.
The independent A-A's `REQUEST_CHANGES` findings are incorporated as scope
constraints below. This revision remains unaudited by its author.

## Grounded current state

The current role-separation checks compare caller-configured `worker_id` strings:

- `hive_arango_queue.py:579-592` creates a runtime attempt packet identified by
  task and worker label, but it has no process-instance identifier.
- `hive_arango_queue.py:1449-1566` claims a task by writing `worker_id`, then
  creates and attaches the attempt packet in a second database operation.
- `hive_build_worker.py:51-95` emits BuildPackets with a worker label and
  verification key, but no attempt identity or source artifact digest.
- `hive_audit_worker.py:147-206, 209-245` checks worker-label inequality and
  refers to a BuildPacket by `build_key`.
- `hive_promotion_worker.py:86-119, 122-156` checks three worker labels and
  refers to an AuditPacket by `audit_key`.
- `hive_arango_queue.py:780-890, 1035-1112` validates those labels and fetched
  packet references, but does not bind build/audit/promotion to a claimed
  runtime attempt or verify a source-artifact digest.
- `tests/test_hive_worker_separation.py` checks label comparisons, including
  mocked database reads. It does not establish distinct runtime processes or
  artifact-content binding.

Thus, different configured labels currently satisfy the separation check even
if they are supplied by one process, and callers can choose those labels. The
current code does not establish that
the build evidence certifies an immutable source snapshot: the ordinary
VerificationPacket emitted in `hive_bee.py:1098-1128` contains status and Lean
output, and its execution intent freezes goal/tactic/import/context fields,
not a source-tree snapshot digest.

## Causal dependency order

```text
Internal process instance ID
            │
            ▼
Atomic claimed attempt (task key + attempt ID + instance ID)
            │
            ▼
Build evidence bound to attempt + immutable source snapshot digest
            │
            ▼
Audit references exact BuildPacket key + digest and uses another instance
            │
            ▼
Promotion references exact AuditPacket key + digest and a third instance
```

The source-snapshot digest is a prerequisite for a claim that the audit
inspected the same source that was compiled. A hash of a BuildPacket or its
stdout alone is only an evidence-packet hash; it is not a source-artifact hash.

## Minimal implementation contract

### 1. Runtime and attempt identities

Generate `runtime_instance_id` inside each worker process at startup using a
cryptographically random UUID. Do not accept it from a CLI argument, task
payload, environment override, or caller-supplied worker label. Keep
`worker_id` as an operational display/routing label only.

At claim time, generate a fresh `attempt_id`. Extend the claim API to receive
the internally created instance ID and write `worker_id`, `runtime_instance_id`,
`attempt_id`, and the running attempt record in the same atomic AQL update. The
subsequent packet emissions must copy the exact values from the returned claim
record, not regenerate or accept them from arbitrary inputs. Reject stale
attempts when the task's current attempt ID no longer matches.

Suggested attempt identity:

```text
attempt_id = UUID generated at each successful claim
runtime_instance_id = UUID generated once per worker process
```

Reclaiming a lease creates a new attempt ID. A process may retain one runtime
instance ID across several sequential attempts.

### 2. Immutable artifact identity

Before a BuildBee runs the locked build, create an immutable, deterministic
manifest of the exact owner source inputs and relevant build configuration. The
manifest must include normalized repository-relative paths and SHA-256 content
digests; its canonical serialized form receives `artifact_sha256`. The build
must operate on that snapshot or verify the working inputs still match the
manifest immediately before and after compilation. The present BuildBee path
does not implement this snapshot step, so this remains an implementation
prerequisite, not an existing guarantee.

The BuildPacket should contain:

```json
{
  "attempt_id": "...",
  "runtime_instance_id": "...",
  "artifact_sha256": "sha256:...",
  "artifact_manifest_key": "..."
}
```

The manifest itself should be an immutable packet with a schema/version and
canonical content digest. Validators recompute the digest from the referenced
manifest rather than trusting a copied digest field. BuildPacket `packet_key`
continues to identify the packet; `artifact_sha256` identifies the compiled
source snapshot. These are different identities.

### 3. Exact audit lineage and process separation

An AuditPacket must reference the fetched BuildPacket by both `build_key` and
`build_packet_sha256` (canonical digest of its immutable content), and copy
`attempt_id`, `artifact_sha256`, and producer `runtime_instance_id` from that
fetched packet. The audit process supplies its internally generated
`runtime_instance_id`. A passing audit is rejected unless:

- the fetched BuildPacket key and canonical digest match the AuditPacket;
- the manifest digest recomputes to the BuildPacket's artifact digest;
- the build and audit attempt/artifact identities agree;
- producer and auditor runtime instance IDs are nonempty and different;
- the AuditPacket's own runtime ID equals the ID in its claimed attempt record.

An AuditPacket that merely carries different `worker_id` labels is not evidence
of runtime separation. A process-local UUID detects accidental same-process
reuse under different labels, but remains self-reported data; it does not
authenticate the process or establish independent reasoning. Legacy packets
without these fields may remain readable for historical inspection, but cannot
authorize a new passing audit.

### 4. Exact promotion lineage and process separation

A PromotionDecisionPacket must reference the fetched AuditPacket by key and
canonical packet digest, and copy the exact build key, build digest, artifact
digest, and attempt identity from it. Its runtime ID must equal its own claimed
attempt record and differ from both producer and auditor runtime IDs. Validate
this against fetched packet documents in `validate_packet_database_invariants`,
not just against packet-local copies.

This proposal addresses lineage and process separation only. In the current
implementation, `hive_audit_worker.py:239` emits `promotion_allowed: false`,
while `hive_promotion_worker.py:115-119` requires that field to be true before
promoting. Current AuditBee output therefore cannot authorize promotion. This
proposal does not change that policy or close the separate promotion-authority
gap.

### 5. Packet immutability / hash definition

Add a shared canonical digest helper with a versioned canonicalization rule:
sorted object keys, UTF-8, compact separators, and explicit exclusion only for
the digest field itself. Avoid hashing a packet after adding a self-referential
digest. Validators must recompute and compare. A fetched key alone is
insufficient if storage permits overwrite under an existing key; database
invariants should verify the stored document's canonical digest at consumption.

## Composite `hive_swarm.py` scope correction

`hive_swarm.py:100-121` dispatches generator, critic, and auditor roles through
the same `SwarmConfig` and same `call_openai_compatible` endpoint/model
configuration. `hive_swarm.py:247-250` and `300-302` call the auditor role
inside the same `run_one` process that generated/criticized/formalized the
tactic. The role prompt is not a process or identity boundary. Therefore this
path must not label its model-produced auditor response as an independent
AuditBee/QMS audit or use it to satisfy an independent audit gate.

Smallest honest options, in order:

1. Remove the auditor role from the composite acceptance path. Record it as a
   `self_review`/`composite_review` note with `promotion_allowed = false`, and
   route successful Lean/build evidence to the separate `audit.semantic` queue.
2. Or make `hive_swarm` stop after generation/critique/Lean checking and enqueue
   the exact immutable artifact for a separately claimed AuditBee attempt.

Do not claim that selecting a different model name or role prompt alone proves
independent reasoning. A distinct runtime process is a mechanically checkable
same-process-reuse signal only; it does not authenticate process identity or
establish cognitive independence. It also does not satisfy the repository's
QMS requirement for separate author and audit agent instances. A distinct Hive
process can enforce a workflow boundary, but independent QMS audit still
requires a distinct auditor agent/context and read-only audit evidence.

## Required tests for a later implementation

These are acceptance targets for a separate QA-A, not tests run for this
proposal:

1. Different `worker_id` labels but identical runtime IDs reject at audit.
2. Equal runtime IDs reject even when all three worker labels differ.
3. Audit with mismatched BuildPacket key, packet digest, attempt ID, or artifact
   digest rejects after database fetch.
4. Mutated source manifest content with the original claimed digest rejects.
5. Promotion with a copied/forged auditor ID, build digest, or audit digest
   rejects after database fetch.
6. A reclaim creates a fresh attempt ID; a stale worker cannot emit a passing
   packet for the reclaimed attempt.
7. Legacy packets remain inspectable but are rejected for new passing audits
   and promotions.
8. `hive_swarm` cannot produce an independent-audit disposition from its
   in-process auditor prompt.

## Explicit limitation

Runtime IDs and digests improve process separation and evidence binding under
the repository's normal trusted-worker/database model. Since a privileged
operator or compromised process can alter the database or fabricate packet
contents, these fields alone do not provide cryptographic attestation of host
identity, human identity, model reasoning independence, or execution isolation.
If those properties are required, a separately specified signing key and
attestation boundary is needed; it is outside this minimal change.
