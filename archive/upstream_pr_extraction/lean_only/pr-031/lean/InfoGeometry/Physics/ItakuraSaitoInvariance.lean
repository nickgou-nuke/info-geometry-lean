namespace InfoGeometry.Physics.ItakuraSaitoInvariance

/-!
# Itakura-Saito Invariance — owner surface

This file is a thin owner facade. The verified definitions it re-exports
live in `InfoGeometry.Arithmetic.WeylArithmeticDivergence`; the
operator-bridge instantiation lives in
`InfoGeometry.Algebra.CuntzFibonacciBraidInclusion`.

## Verified native pieces already in repo
- `InfoGeometry.Arithmetic.WeylArithmeticDivergence.itakuraSaito`
- `InfoGeometry.Algebra.CuntzFibonacciBraidInclusion.trace_conj_matrixToCuntz`
- `InfoGeometry.Algebra.CuntzFibonacciBraidInclusion.log_potential_preserved`
- `InfoGeometry.Algebra.CuntzFibonacciBraidInclusion.inv_pairing_conj_preserved`
- `InfoGeometry.Algebra.CuntzFibonacciBraidInclusion.itakuraSaito_invariance_under_conjugation`

## Residual closure debt
- `inv_pair_conj_semiring`: lemma 3 in the current generic `[Semiring A] [Inv A]`
  form is not provable without extra group/algebraic structure assumptions.
  Next step: lift to `[DivisionMonoid A]` or restrict to the operator/image
  types built by `CuntzAlg` and `Matrix.toLinAlgEquiv`.
- `itakuraSaito_concrete_conjugation`: compose `log_potential_preserved`,
  `trace_conj_matrixToCuntz`, and `inv_pairing_conj_preserved` into an
  explicit divergence-invariance theorem for `WeylArithmeticDivergence.itakuraSaito`
  on matrix/socket inputs.
- `pin55_carrier_reindex_comm`: needed to close
  `InfoGeometry.Lie.Pin55KreinConformalBridge`.
-/

