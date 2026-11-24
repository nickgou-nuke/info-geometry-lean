# Focused Zorn Clifford triality verification

This profile checks the exact native owner sources with the repository's
unchanged Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` pins. It is separate from the root
package build and publication gate.

## Run

Put the pinned Lean/Lake runtime on `PATH`. Existing dependencies can be used
without copying their caches. `--package-root` must contain all nine exact
Git dependencies in the maintained `real-matrix-split` manifest. Every pin,
tracked-source cleanliness, untracked Lean/config file, and toolchain is checked.

```bash
python3 verification/zorn-cl44-triality/check.py \
  --work /absolute/path/outside/repository/zorn-cl44-build \
  --package-root /absolute/path/to/exact-pinned/packages \
  --module InfoGeometry.Canonical.ZornSignedConvention \
  --module InfoGeometry.Canonical.ZornCl44Triality \
  --module InfoGeometry.Canonical.ZornCl44TrialityDerivation \
  --module InfoGeometry.Canonical.ZornCl44TrialityOrthogonal \
  --module InfoGeometry.Canonical.ZornCl44Faithfulness \
  --module InfoGeometry.Canonical.ZornCl44PrimalDual \
  --module InfoGeometry.Canonical.ZornCl44TrialityBoost \
  --module InfoGeometry.Canonical.ZornCl44NullIncidence \
  --module InfoGeometry.Canonical.ZornCl44DerivationInvariant \
  --phase final
```

Use `--phase build` while repairing elaboration. Use `--no-wait` only to
fail immediately when the shared compiler lock is occupied. It never runs
around that lock. The work directory must be empty or already belong to
this same source checkout.

The maintained hydration route for a fresh development checkout is:

```bash
python3 verification/real-matrix-split/check.py exe cache get
```

## What is checked

The runner copies the selected owners' exact transitive repository source
closure into an independent Lake project, uses native Lake package overrides,
and holds the maintained shared build lock throughout the serial transaction.
It records every command and exit status, validates the runtime version,
and preserves separate logs for every attempt.

The final phase builds each source module, freshly elaborates the selected
owners with warnings treated as errors, and generates a complete declaration
audit through the maintained `reviewed_audit_source` implementation. The
audit rejects partial or unsafe declarations and transitive axioms beyond
`propext`, `Classical.choice`, and `Quot.sound`. It reconciles the exact
declaration counts for every selected owner.

After the run, source, control, project, dependency, and repository-commit
checks must still match. A receipt with `focused_passed` covers this selected
surface only. The receipt explicitly leaves the root build, publication gate,
and independent semantic-review status outside its certification.

Use the explicit nine-owner selection above for the complete current change.
The runner's historical default selects only the original triality and
derivation owners; a default run does not certify the extension.

The verbatim first input is `intake.txt`; the second is
`intake-primal-dual-20261124.txt`. Mathematical contracts and correction
ledgers are in `docs/ZORN_CL44_TRIALITY_CONTRACT_20261124.md` and
`docs/ZORN_PRIMAL_DUAL_GEOMETRY_CONTRACT_20261124.md`.
