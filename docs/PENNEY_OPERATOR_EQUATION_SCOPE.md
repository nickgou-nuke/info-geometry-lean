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

Kernel-verified (`lake build`, `3161` jobs, `0` errors, `0` warnings, `0` `sorry`/`admit`/custom axioms) and screened cleanly by `opengauss_screener.py --strict` (`0` traps) and `check_no_hypothesis_mandate.py` (`PASSED`).

## Constructive finite covariance, Hilbert–Schmidt positivity, and skew-adjoint conservation (2026-10-24)

- `Canonical/AlbertCayleyDickson.lean` (`SplitQuaternion`):
  - `bruhatS_left_intertwines_peirce_and_wheelJ`: constructive zero-hypothesis intertwining of `(peircePlus, peirceMinus, wheelJ)` by the Tits–Bruhat element `bruhatS`.
  - `star_wheelJ`, `wheelJ_gram_deriv_zero`, `wheelJ_peirce_sector_gram_deriv_zero`: constructive zero-hypothesis skew-adjointness `star wheelJ = -wheelJ` and exact `2 × 2` matrix Gram conservation (`star (wheelJ * χ) * χ + star χ * (wheelJ * χ) = 0`) on the full carrier and on each right-isospin Peirce sector.
  - `trace_star_mul_self_eq_sum_sq`, `trace_star_mul_self_peircePlus_eq_sum_sq`, `trace_star_mul_self_peirceMinus_eq_sum_sq`, `trace_star_mul_self_peircePlus_nonneg`, `trace_star_mul_self_peirceMinus_nonneg`, `trace_star_mul_self_nonneg`: constructive zero-hypothesis sum-of-squares expansion and nonnegativity of the Hilbert–Schmidt Gram trace and its positive/negative right-isospin sector projections.
- `Canonical/PenneyLeftCovariance.lean`:
  - `leftConjugate`, `leftConjugate_intertwines`, `leftIntertwines_leftConjugate`, `leftConjugate_residual_transport`, `coupled_leftConjugate`, `bruhatS_leftIntertwines_peirce`: constructive unit-similarity and Tits–Bruhat left intertwiners alongside `coupled_left_intertwines` and `right_sector_transport`.
- `Canonical/PenneyPositiveDensity.lean`:
  - `trace_transpose_mul_self_eq_squaredEntryTrace`, `trace_transpose_mul_self_nonneg`, `splitQuaternion_sector_gram_trace_nonneg`, `splitQuaternion_wheelJ_gram_conservation`: bridges `squaredEntryTrace x` directly to the matrix Gram trace `Matrix.trace (xᵀ * x)` and exposes sectorwise positivity and `wheelJ` matrix Gram conservation on `SplitQuaternion ℝ`, alongside `temporalDensity_hasDerivAt_zero`.

The next genuine missing targets are a native, representation-correct Lorentz action with transformed momentum and mass; a nontrivial indefinite `Spin(1,3)` bilinear invariant coupled to that action; and Penney's spatial current with `∂ₜρ + ∑ᵢ∂ᵢjᵢ=0`. Do not identify the squared-entry trace with the physical current without a separately proved equality.
