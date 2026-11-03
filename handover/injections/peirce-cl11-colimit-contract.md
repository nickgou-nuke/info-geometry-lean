# Peirce powers in the `Cl(1,1)` tower colimit: theorem contract

## Precise claim

For a finite stage `Stage n` of the repository's `Cl(1,1)` matrix tower and
coefficients `a c : Stage n`, the off-diagonal matrix
`[[0, a], [c, 0]]` has even powers with diagonal entries `(ac)^k` and `(ca)^k`,
and odd powers equal those even powers multiplied on the right by the original
off-diagonal matrix. Applying the canonical ring map `ofStage n` entrywise
preserves both formulas in matrices over the algebraic direct-limit carrier.
The finite-stage map is injective.

## Carriers and owner declarations

- `InfoGeometry.OperatorAlgebra.OperatorMobiusAction.OperatorMatrix A` is
  `Matrix (Fin 2) (Fin 2) A`.
- `InfoGeometry.OperatorAlgebra.ThermodynamicSL2OperatorLift` owns
  `peirceOffDiagonalGenerator`, `peirceEvenPower`, and the kernel-proved
  `peirceOffDiagonalGenerator_pow_even` / `_pow_odd` identities over arbitrary
  `[Ring A]`.
- `InfoGeometry.Clifford.Cl11TensorTowerLimit.Stage n` is the finite matrix
  stage; `Limit` is its existing algebraic direct limit; `ofStage n` is the
  canonical ring map.
- `InfoGeometry.Clifford.Cl11StarAlgebraColimit.ofStage_injective` proves each
  `ofStage n` injective from the injective tower bonds.
- `InfoGeometry.Canonical.PeirceOperatorCl11TowerBridge` defines the entrywise
  limit-valued Peirce matrix and proves the even/odd formulas and stage-map
  injectivity by these owners.
- `InfoGeometry.Canonical.SplitCliffordTensorBridge` owns the finite split Bott
  factorization, including `splitCl55_headCl11TensorCl44Equiv` and its head/tail
  factor readbacks.

## Scope boundary

The new bridge transports `M₂(Stage n)` into `M₂(Limit)`; it does not identify
that matrix ring with `Stage (n + 1)`, nor assert that a shifted algebraic tail
is equivalent to the entire limit. It does not identify the algebraic limit
with a topological completion, and it does not assert a new `Cl(r,r) ⊗
Cl(∞,∞)` algebra equivalence. Such claims need their own explicit carrier maps
and proofs.

## Verification

`lake build InfoGeometry.Canonical.PeirceOperatorCl11TowerBridge` completed
successfully through `tools/infra/run_locked_lake_build.py` with the repository
shared build lock.
