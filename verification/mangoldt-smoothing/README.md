# Finite Mangoldt smoothing verification

This package checks `InfoGeometry.Arithmetic.FiniteSmoothedMangoldt` and its
axiom/boundary companion using the root repository's Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` pins. It reads the actual sources in
`../../lean`; it contains no replacement mathematical declarations.

From the repository root:

```bash
python3 verification/mangoldt-smoothing/check.py exe cache get Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
python3 verification/mangoldt-smoothing/check.py build InfoGeometry.Arithmetic.FiniteSmoothedMangoldtAudit
python3 verification/mangoldt-smoothing/check.py env lean lean/InfoGeometry/Arithmetic/FiniteSmoothedMangoldtAudit.lean
```

The build closure consists of the existing `FiniteSpinAlgebra` and
`PrimeDistributionLaw` owners, the new smoothing owner and its audit, plus
their pinned Mathlib imports. The wrapper serializes work through the shared
build lock. The audit covers all eighteen new declarations and checks the
zero boundary and a strictly positive prime contribution.

Read [the source and scope audit](../../docs/ALPOGE_REMARK_AUDIT.md) for the
mathematical contract. These finite arithmetic results do not verify the
external RH/GRH proof or the repository's complete default-target build.

The independent [validation record](validation.json) accepts this finite scope:
the focused build with `--wfail`, fresh owner check, and all eighteen axiom
checks passed with zero compiler warnings. Two boundary-lemma warnings from
the heuristic semantic scanner are retained and explicitly classified.

The separate root `InfoGeometry.All` build was attempted and stopped at the
missing `HomotopyHypothesis` path dependency. That integration failure does not
change the observed focused proof result and prevents a root-build certificate.
