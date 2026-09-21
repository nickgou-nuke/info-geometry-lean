# Finite Cuntz synthesis

Owner: `lean/InfoGeometry/Exceptional/CuntzFiniteSynthesis.lean`.
Tests: `lean/InfoGeometry/Exceptional/CuntzFiniteSynthesisTests.lean`.

This module implements the finite synthesis without duplicating a Cuntz class,
split-quaternion carrier, or interval-projection algorithm. It uses the current
`CuntzArchimedeanColimit` algebraic owner, `SplitQuaternionMatrixModel`, Mathlib's
`Set.projIcc`, and `SimplexQuadraticResponse`.

## Results

- Conceptual prerequisites form a poset of finite sets under inclusion. Cuntz
  orthogonality and split-null geometry are explicitly incomparable branches;
  this poset is not an extracted Lean declaration-dependency DAG.
- Multiplication on either side preserves the zero Cuntz cross term under the
  stated isometry and partition assumptions in a native star ring.
- Native matrix determinants agree with the existing split-quaternion norm.
  Equal negative-sign coordinates have strictly negative determinant away from
  zero; opposite-signature coordinates give a genuine nonzero square-zero matrix.
- The interval projection fixes exactly `[0,1]`, is idempotent, maps onto that
  interval, and is not injective. Its fixed set is not the singleton `{1/2}`.
- The real quadratic `point * (1 - point)` is at most `1/4`, with equality
  exactly at `1/2`. Existing quadratic-response results supply the bound and
  completed-square identity.

The source neither represents full Cuntz isometries as finite matrices nor
constructs an Archimedean colimit. No detector dynamics, RH, Maass eigenvalue
bound, or physical realization is inferred from these finite statements.

## Verification status

All theorem bodies are supplied, with no added axioms or proof placeholders.
The test module includes concrete nonzero witnesses, counterexamples, and
`#print axioms` for every public theorem. Kernel compilation and axiom-output
inspection have not yet run: the shared repository build lane is occupied.
No concurrent compiler or additional waiting build was started.

After the existing build lane becomes available:

```sh
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Exceptional.CuntzFiniteSynthesisTests
```
