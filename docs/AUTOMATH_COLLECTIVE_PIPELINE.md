# AutoMath Collective Pipeline

## Purpose

AutoMath is a candidate-generation and evidence-collection adapter for the
repository's existing Archon/Pi theorem queue. It is not a second mutable task
queue, a theorem authority, or an automatic source-promotion mechanism.

The current entry points are `tools/infra/agent_orchestrator_queue.py` for
queued theorem work and `tools/infra/automath_pipeline_main.py` for processing
an explicit hypothesis batch. AutoMath must not create a parallel queue or
change the owner-source/build authority.

## Division of work

```text
Archon/Pi task queue
  ├─ Researcher: locate owner declarations and bounded source context
  ├─ Memory reader: exact-provenance lookup when an approved reader is configured
  ├─ Algebraist: provide a task-specific SymPy witness when useful
  ├─ ChatGPT Pro: suggest or critique a candidate through the guarded lane
  ├─ Formalist: inspect the proposal and make any source edit
  ├─ Lean gate: check serially under the shared build lock
  ├─ Static gate: run the semantic-vacuity screen (not a full QMS audit)
  ├─ Human reviewer: approve owner-file promotion when appropriate
  └─ Archivist: append run, candidate, environment, and audit evidence
```

Research, memory lookup, and symbolic exploration may proceed independently.
They join before a candidate is proposed. The formalizer then works from the
actual owner context. Lean and semantic-vacuity outcomes attach to the exact
candidate hash. A separate QMS audit is not yet run by this adapter. Only the
human-reviewed source change enters the owner module and normal build graph.

## Evidence boundaries

- Lean source and the Lean kernel decide theorem truth.
- Pantograph InfoTree/replay, Arango retrieval, SymPy, and ChatGPT are
  navigation or proposal evidence. They do not establish theorem validity.
- An oracle response is never applied to an owner file by this pipeline.
- A candidate lives at
  `tmp/oracle_candidates/automath/<hypothesis>/<sha256>.lean`; writes are
  content-addressed and do not replace earlier proposals.
- `sorry`, `admit`, `axiom`, `unsafe`, and obvious `True := by trivial`
  candidates are rejected before Lean checking.
- The Lean check owns the repository's shared build lock. The semantic
  vacuity gate then screens the exact same candidate file. This is not reported
  as a complete QMS audit.
- Candidate records carry an integrity-checkable receipt bound to the candidate,
  source snapshot, toolchain, Lake inputs, Git head, and gate outputs. Receipt
  digests detect changed content but are not signatures or proof certificates.
- An input may set `metadata.axiom_audit_declarations` to a list of fully
  qualified Lean declaration names. AutoMath then re-elaborates the candidate
  under the shared lock and runs `#print axioms` for exactly those names. The
  raw Lean output, requested names, return code, and digest are recorded. An
  absent list is `not_requested`; audit errors remain visible and are never
  treated as an empty axiom set.
- A missing SymPy witness is recorded as `not_supplied`, not as a CAS pass.
  Supplied witnesses must be explicit `.py` paths under `tools/sympy/`; their
  hashes are recorded with the result.
- Arango records are append-only candidate observations. A successful record
  has `authority = candidate_record_not_proof_authority` and a status that
  explicitly awaits review. Database failure falls back to a local JSONL
  observation; it does not change Lean source.

## Run identity and replay fields

Each candidate observation should retain:

- `run_id`, hypothesis ID, owner apex, resolved owner path, and owner source
  SHA-256;
- immutable candidate path and candidate SHA-256;
- Lean toolchain, `lakefile.lean`, Lake manifest SHA-256, and observed Git HEAD;
- separate Lean and semantic-vacuity return codes and output hashes;
- hashes of any task-specific SymPy witness scripts;
- oracle task ID, response text hash, and advisory verdict;
- timestamps and a record type that distinguishes proposals from accepted
  owner theorems.

Do not merge these identities into a single opaque “proof hash.” The AutoMath
fields are identity fragments, not a replayable Lean environment fingerprint:
imported OLean hashes and a computed Pantograph context fingerprint are not
currently attached. Pantograph environment/session fingerprints remain
authoritative for Pantograph captures. AutoMath does not yet retrieve Arango or
Pantograph memory automatically; any future reader must require exact source
and context fingerprints and record matched event keys. This avoids claiming a
replay that was never performed.

Candidate receipt readers validate the digest and compare bound fields with
the enclosing record before exposing the receipt. This only checks local record
integrity; it does not authenticate the writer, rerun Lean, or authorize
promotion.

## Oracle transport

The Tampermonkey bridge uses the local HTTP polling service, not a WebSocket.
AutoMath invokes it only while holding the shared ChatGPT lane guard. A missing
final response is an unresolved readback state: preserve the busy marker and
recover the visible response before sending another prompt. Do not use the
legacy direct browser-harness fallback or stack requests.

The prompt receives the resolved owner module (or a bounded excerpt for a very
large module), treats the apex as untrusted input, and requests `NO_CANDIDATE`
when definitions or assumptions are missing. Oracle claims such as “verified”
or “breakthrough” have no effect on gate outcomes.

## Promotion protocol

1. Retrieve the exact candidate and provenance record.
2. Inspect the owner theorem and candidate for scope, assumptions, and
   mathematical honesty.
3. Apply a surgical owner-file patch; preserve existing source and staged work.
4. Run the narrow Lean check or locked target build, then QMS gates.
5. Record the accepted source snapshot and build evidence. Never promote merely
   because the candidate compiled in isolation or appeared in Arango.

The existing agent orchestrator remains responsible for scheduling theorem
tasks. GEPA may analyze run outcomes and propose quarantined workflow changes;
it must not silently mutate this protocol or the active Archon workflow.
