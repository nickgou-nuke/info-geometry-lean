# Shared-formalism owner verification

The [theorem contract](../../docs/SHARED_FORMALISM_BOUNDARIES_CONTRACT.md)
records the mathematical scope, recovery provenance, and verification status.

From the repository root, with the pinned Lean toolchain and dependencies
available:

```bash
python3 verification/shared-formalism/check.py
```

The runner reuses `verification/real-matrix-split` and acquires the repository's
shared build lock for the entire transaction, including child cleanup. It
checks the root/focused toolchain pins and the nine focused Git dependencies
against their corresponding root-manifest revisions, including actual HEADs
and tracked cleanliness. It then builds the two owners in separate sequential
Lake commands, checks each source afresh with warnings as errors, and runs the
canonical exhaustive declaration-ownership
audit. Generated and private declarations are included; unsafe/partial
declarations and axioms outside `propext`, `Classical.choice`, and `Quot.sound`
are rejected.

Receipts and per-run logs go to `artifacts/verification/shared-formalism` by
default. Use `--output-dir` to select another location. The receipt first marks
the invocation queued, then running, failed, or passed; source and pin snapshots
are taken after lock acquisition. The runner checks that its enumerated owner,
helper, and configuration inputs and focused dependency identities remain
unchanged before recording success. Root external path dependencies and the
entire imported source closure are outside that snapshot. An interrupted run
may leave an incomplete receipt; only a completed `passed` receipt records
success.

This runner was reconstructed on 2026-11-24 after the prior scratch checkout
was unavailable. The two Lean owners were recovered byte for byte, as recorded
in the contract; the runner itself is not claimed as byte-identical recovery.
The owner-build commands were subsequently serialized after an interrupted
combined build; the verification scope and all acceptance checks are retained.

Focused-owner verification is separate from the required root-package
publication gates and independent semantic review. It does not establish
analytic/geometric extensions or equivalence of physical theories.
