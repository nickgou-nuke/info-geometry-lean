# Pauli powers versus tensor products

`Nuclear/SpinorMultipoles.lean` reuses the real Witt creation atom and binary
matrix tensor stages from `Clifford/Cl11TensorTower.lean` and `TowerMatrix.lean`.
It does not define an operator to be a spherical harmonic by renaming it.

The single-site raising matrix squares to zero. Consequently its ordinary
cube is zero. Its three-fold Kronecker tensor product is instead a nonzero
operator on an eight-dimensional real spinor space. A specific matrix entry
equals one at every tensor stage, supplying a nonzero witness. Every positive
tensor power still squares to zero, so it cannot itself be an order-three
clock or shift operator.

The scalar cyclotomic identity is reused from `AlgebraicPolarization.lean`.
It requires a nontrivial third root in a ring without zero divisors; it is not
an unrestricted matrix cancellation theorem. No real scalar satisfies
`root^2 + root + 1 = 0`. Real matrix rotations can encode such phases, but the
nilpotent raising tensor is not such a rotation.

These statements do not identify a spherical harmonic, prove tracelessness,
select a nuclear equilibrium shape, or establish stability or absence of
dissipation. Such conclusions require additional representation-theoretic and
dynamical definitions and theorems. A cyclic root identity alone supplies none
of them.

## Verification

The source includes full proof scripts and regression examples without proof
placeholders. Kernel verification is pending the shared build lane; successful
compilation is not yet claimed.

```
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Nuclear.SpinorMultipolesTests
```
