# Codex review: OpenGauss/Hive bounded pilot runner

## Review status

The runner in `tools/infra/opengauss_hive_pilot.py` is a credible bounded,
fail-closed verification runner. It is not yet sufficient evidence for final
promotion without the additional controls below.

The runner correctly provides:

- contract validation before later gates;
- candidate snapshot hashing;
- scratch/ and tmp/ sandbox restrictions;
- symlink rejection for candidates;
- bounded subprocess timeouts;
- rejection and timeout manifests;
- generated `#print axioms` checking;
- an explicit allowed axiom set of `propext`, `Classical.choice`, and
  `Quot.sound`;
- schema-validated A-A and QA-A evidence;
- optional queue heartbeat/claim/expiry/reclaim/completion smoke testing;
- default `hold` behavior;
- no owner-file writes;
- Archon recorded as orchestration-only.

## Critical issues to close

### 1. Bind the candidate to the theorem declaration

The runner checks that the candidate compiles, but it does not yet establish
that the candidate contains the declaration described by the Ground-Truth
Contract. An empty or unrelated Lean file must not be able to pass refutation,
Lean compilation, and a zero-declaration axiom audit.

Require at least one candidate declaration and bind it to the contract's
qualified declaration and target expression. Record the candidate declaration
set in the binding artifact and reject a mismatch.

### 2. Preserve full hashes in Hive lineage

The Hive smoke currently uses hash prefixes for queue fields:

```python
contract_hash[:32]
candidate_hash[:32]
```

Prefixes may be display keys, but they are not sufficient provenance. Store the
complete contract hash and candidate hash in a validated contract or packet
record referenced by the task. The smoke artifact must expose both the full
hashes and the queue/task key.

### 3. Separate queue smoke from packet-lineage smoke

The current `--hive-smoke` test verifies:

```text
heartbeat → enqueue → claim → expiry → reclaim → complete
```

This is valuable, but it does not yet verify insertion and dependency lineage
for theorem candidate, Lean verification, build, audit, and promotion packets.
Call it a lease/queue smoke test. Add a separate opt-in packet-lineage smoke,
or explicitly record that packet lineage remains untested.

### 4. Make early rejection identities collision-resistant

Early rejection records must contain a raw contract-file hash and a
collision-resistant run identifier. A second-level timestamp alone is not
safe under parallel execution.

### 5. Strengthen independence evidence

Distinct agent, session, origin-run, and context hashes are useful integrity
checks, but metadata alone does not prove genuine A-A/QA-A independence.
Evidence should also bind:

- input packet hash;
- source snapshot hash;
- exact tool invocation;
- execution environment/toolchain hash;
- parent-context exclusion or fresh-context receipt;
- reviewer-specific output hash.

The result should be described as declared independence until the runtime can
prove fresh, separate contexts.

### 6. Require a distinct promotion context

`--allow-promotion` is an explicit operator flag, but it is not itself a
validated promotion packet. A final promotion decision should require a
separate promotion-worker identity and a schema-valid promotion record that
references the audit, QA, Lean, build, and source evidence.

The runner may record `decision=promote`, but it must not integrate owner source
or imply that the flag alone establishes mathematical authority.

### 7. Keep `hold` distinct from acceptance

The runner returns a successful process exit for both `promote` and `hold`.
That is acceptable for a scheduler, but Archon must consume the manifest
state. Exit code zero must never be interpreted as QMS acceptance.

## Required acceptance sequence

Before any promotion claim, verify:

```text
contract validates
→ candidate declaration matches contract
→ full hashes are persisted
→ refutation passes
→ Lean passes on the immutable snapshot
→ explicit #print axioms passes
→ locked build passes where required
→ A-A schema and identity checks pass
→ QA-A schema and identity checks pass
→ optional Hive lease smoke passes
→ packet lineage is replayable
→ explicit promotion packet is accepted
```

The first successful pilot should remain finite, serial, and replayable. No
full swarm or toolchain upgrade is justified until the candidate-to-contract
binding and packet-lineage gaps are closed.

## Implementation response

The reviewed gaps are now addressed in
`tools/infra/opengauss_hive_pilot.py`.

- Candidate binding now requires the contract's qualified declaration to occur
  in the immutable candidate snapshot, with a result type matching the
  contract target expression. Empty or unrelated candidates are rejected.
- Hive queue smoke records complete contract and candidate hashes rather than
  truncated prefixes. The final manifest records the queue and task key.
- Queue leasing and packet lineage are separate checks. The opt-in
  `--packet-lineage-smoke` validates a causal candidate → Lean → build → audit
  → promotion chain against the repository Hive schemas and checks its
  references and hashes.
- A-A and QA-A evidence is schema-validated and must bind the current input,
  contract, run, snapshot, tool invocation, environment fingerprint, reviewer
  output, and a declared fresh context. These metadata checks establish
  declared independence; they do not claim to prove the reviewer's internal
  context.
- Promotion requires a separate schema-valid promotion-worker record supplied
  with `--promotion-evidence`. The operator flag alone cannot produce an
  accepted result.
- Early rejection manifests use a microsecond timestamp plus a content-derived
  fingerprint. Timeout and rejection manifests remain distinct.
- The manifest now distinguishes scheduler completion (`process_exit_code=0`)
  from QMS acceptance (`qms_acceptance=accepted` only after promotion).

Validation actually run after these changes:

```text
python3 -m py_compile tools/infra/opengauss_hive_pilot.py       PASS
tools/infra/opengauss_hive_pilot.py --help                     PASS
git diff --cached --check                                       PASS
```

No Hive mutation or full Lake build was performed in this pass. Both remain
explicit opt-in operations. A stale contract was previously rejected and
produced a collision-resistant rejection manifest, confirming the fail-closed
early-error path.
