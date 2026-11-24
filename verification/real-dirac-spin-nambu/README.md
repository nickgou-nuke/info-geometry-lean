# Real Dirac, spin Casimir, and associative Nambu verification

This is the focused verification entry point for the recovered packet stacked
on PR #429. The [source contract](../../handover/injections/real-dirac-spin-nambu-20261124.md)
records the exact claims, conventions, recovered hashes, adopted base, and
interpretation limits.

## Run

From an independent checkout with the repository-pinned Lean runtime and
dependencies available:

```bash
python3 verification/real-dirac-spin-nambu/check.py \
  --repo . --output artifacts/verification/real-dirac-spin-nambu/run-001
```

The runner reuses `verification/real-matrix-split` as its execution package,
with explicit module targets. It does not select that package's default
matrix-split suites and does not depend on the missing earlier core/phase
packet. The focused package must retain the same Lean and Git dependency pins
as the root manifest: Lean `4.34.1`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, and the accompanying pinned packages.
Choose a new output directory for each run; existing reports are not overwritten.

## Coverage

The five checked sources are:

- `InfoGeometry.Canonical.RealPauliPfaffianKernel`, including the two added helpers;
- `InfoGeometry.Algebra.AssociativeNambuOperators`;
- `InfoGeometry.Canonical.RealDiracLinearLift`;
- `InfoGeometry.Canonical.RealDiracSpinCasimir`;
- `InfoGeometry.Canonical.RealDiracNambuChecks`, containing six regressions.

The runner checks source hygiene and matching dependency pins, captures source
hashes, builds the explicit targets under the repository's shared lock, checks
each source in a fresh Lean process with warnings treated as errors, and runs
a fresh `#print axioms` probe. Its inventory includes explicitly named public
heads in the kernel and three new mathematical owners plus ten selected reused
declarations, with duplicates removed. The existing inventory does not enumerate
private or generated heads independently; their axiom dependencies are covered
transitively through the audited public heads. Regression examples are checked
by fresh file elaboration.

The allowed reported axioms are `propext`, `Classical.choice`, and `Quot.sound`.
Missing runtime or package prerequisites produce a nonzero blocked result.
An exit-zero verification result requires all selected compilation and axiom
checks to succeed without source changes during the run. Source inspection,
declaration inventory, compilation, and semantic review remain separate evidence.

## Draft publication status

All four sources were recovered with exact SHA-256 matches to the retained packet.
Three retain those bytes. The LinearLift's alternating-form proof now explicitly
states the real scalar identity used by `ring`; its statement and native form
are unchanged. The source contract records that separately reviewed repair and
its final hash. The two helper lemmas are newly authored against PR #429's kernel.
Independent source review covers this adaptation. Neither recovery hashes nor
source review establish Lean acceptance.

The prior queued build has no observed completion result in this runtime.
Fresh compilation, axiom acceptance, and the repository publication gate remain
required before merge. The root workspace additionally requires its separately
configured local path dependencies; a focused success would not establish a
full root or whole-repository build. See the PR description for the exact
publication-run commands and observed results.
