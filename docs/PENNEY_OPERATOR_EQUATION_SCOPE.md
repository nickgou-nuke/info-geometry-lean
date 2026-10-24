# Penney (1971) operator-valued octonion formalization — theorem contract

**Source:** R. Penney, *Octonions and Isospin*, Il Nuovo Cimento B 3 (1971), 95–113, supplied PDF.

## Repo owners reused

- `Canonical/AlbertCayleyDickson.lean`: `AlbertStep`, nonassociative doubled product and conjugation.
- `Canonical/CayleyDicksonEmbedding.lean`: additive structure for doubled elements.
- `Canonical/PenneyOctonionIsospin.lean`: earlier right-sector projection and coupled equations.
- Mathlib matrix trace and noncommutative ring tactics.

## New scoped results

1. `PenneyOperatorEquation.associatorDefect`: **exact** discrepancy between `x*(y*z)` and `(x*y)*z` in the existing doubled carrier.
2. `left_factorization_iff_defect_zero`, `first_order_implies_factored_second_order`: factoring the first-order equation through the second operator is legitimate only when the specific associator vanishes. This is the algebraic qualification behind Penney's Eq. (35) and his warning in §7.
3. `coupled_second_order`: derives two ordered second-order equations from the coupled associative equations given commuting mass hypotheses.
4. `coupled_conjugation`: finite algebraic invariance for a supplied inverse pair, **not** an actual representation of the Lorentz group.
5. `minimally_coupled_product`, `minimally_coupled_commutator`: operator-order-preserving expansion and noncommutative curvature term after minimal substitution. No electromagnetic field tensor has been identified with these terms.
6. `PenneyTraceSectors.trace_mixed_sector_zero`, `trace_right_sector_sum`, `trace_conjugation`: finite matrix trace consequences for right-sector decomposition. They are not probability positivity or a conserved current.

## Remaining mathematical obligations

- Explicit operator-valued quaternion/octonion coefficient model matching Penney's Eq. (29), with the required ordered coefficient relations.
- The detailed differential-operator representation, domain conditions and derivation of Eq. (59)–(60) including spin/magnetic coupling.
- Proper Lorentz group action and its *two distinct* quaternion factors as in Eqs. (79)–(82); §8 explicitly warns that the naive single left action on the octonion carrier fails.
- Hermitian adjoint structures, matrix positivity and trace-norm theorem for Eq. (97).
- A conservation theorem `∂_μ j^μ = 0` on a specified differentiable field carrier, with boundary and regularity hypotheses.

## Verification boundary

This branch was edited through GitHub Contents API. This environment has no `lean` or `lake` executable; **none** of the new proofs is asserted kernel-verified. No changes were made to `lake-manifest.json`, `lean-toolchain`, external dependencies, or `All.lean`. Remain draft until narrow compilation, axiom/vacuity audit, and required repository integration gates pass.
