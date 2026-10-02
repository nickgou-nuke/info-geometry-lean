# Local zero certification: scope and proof obligations

Owner: `lean/InfoGeometry/Arithmetic/SarnakLocalCertification.lean`.
Tests: `lean/InfoGeometry/Arithmetic/SarnakLocalCertificationTests.lean`.

The module generalizes the reflection/uniqueness argument already present in
`ActualRiemannXiEntireSchwarzBridge`. Its actual-xi instance reuses that owner's
reflection theorem, and the centered symmetry counterexample reuses
`ZetaSymmetryHeuristicComplement`. It does not replace either owner.

## Mathematical contract

- Dependency contexts use Mathlib's finite-set inclusion partial order. This is
  a declared conceptual dependency model, not an extracted compiler DAG.
- `RiemannSymmetric` requires zero-reflection symmetry, not a functional equation,
  analytic continuation, an Euler product, or a spectral interpretation.
- `CertifiedRegion` contains a set, reflection invariance, and a proof of at most
  one distinct zero. It assumes neither compactness nor openness. It does not
  count multiplicities or assert that a zero exists.
- A covered zero is fixed by reflection and therefore has real part one half.
- A finite family proves only its explicitly covered height range. Global
  confinement requires certificates at every height; no such certificates for
  actual xi are constructed here.
- The tests construct a complete certificate for the nonconstant function
  `s - 1/2`, including its actual zero. Actual xi remains a conditional instance.
- The polynomial `s * (s - 1)` supplies a counterexample to confinement from
  zero-reflection symmetry alone. No certified region can contain its zero at 0.

## Remaining analytic work

Argument-principle counts, contour boundary nonvanishing, certified numerical
error bounds, and coverage of actual xi zeros are not implemented here. An
arbitrary set certificate is not an executable contour-verification algorithm.
There is no proof of RH, GRH, simplicity of xi zeros, or Maass-form sparsity.
In particular, a stipulated logarithmic counting bound must not be named a GRH
consequence without a separate theorem establishing that implication.

## Verification

The test module contains `#print axioms` commands for the public results.
Kernel compilation and axiom-output inspection remain pending while the shared
repository build lock is occupied. Source proof terms are not build evidence.

When the build lane is available, use:

```sh
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Arithmetic.SarnakLocalCertificationTests
```
