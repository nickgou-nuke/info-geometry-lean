# Cuntz/Archimedean proposal: finite algebraic scope

The requested module path is
`lean/InfoGeometry/Exceptional/CuntzArchimedeanColimit.lean`.
Despite its requested filename, it does not construct a colimit or identify one
with the real numbers. It contains only the following finite results:

- Existing Cuntz partition/isometry orthogonality is imported from
  `Canonical/PrimitiveCuntzIsometry.lean`, not defined with another Cuntz class.
- Actual split-quaternion matrices and their multiplication come from
  `Canonical/SplitQuaternionMatrixModel.lean`.
- The proposed coordinates `(0, 0, parameter, parameter)` have determinant
  `-2 * parameter^2`, vanishing exactly when the parameter is zero.
- The different coordinates `(0, parameter, parameter, 0)` give a square-zero
  matrix with zero determinant, nonzero when the parameter is nonzero. This
  correction is explicit; it is not an identification of Cuntz generators with
  finite matrices.
- `intervalProjection` is the clamp `max 0 (min 1 point)`. It lands in `[0,1]`,
  fixes that interval, and is idempotent. It is not a colimit evaluation.

The quadratic form has signature `(2,2)`, not Lorentz signature `(1,3)`.
No detector realization, arithmetic lattice, universal-property identification,
Maass spectral bound, or RH conclusion follows from these results.

The existing `Canonical/CuntzFiniteStageObstruction.lean` must be respected:
two full Cuntz isometries cannot be realized at a finite matrix stage. Boundary
representations and finite matrix units are different constructions.

## Validation

The test module contains concrete corrected and counterexample states,
interval-projection tests, and `#print axioms` commands. Compilation and axiom
inspection are pending behind the active shared repository build lock.

```sh
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Exceptional.CuntzArchimedeanColimitTests
```
