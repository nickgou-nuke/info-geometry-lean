import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SouriauOperatorialLogPotential

/-!
# Noncommutative orthogonal-projector calculus

This module contains the reusable algebraic lemma that remains after the
former evidence packet was audited.  Tautological witness projections and
finite diagonal/scalar readouts are intentionally not exported here.
-/

noncomputable section

namespace InfoGeometry.Canonical.ExplicitWitnessObligations

open scoped BigOperators

/-- Orthogonal finite projector spectral-power obligation. -/
theorem orthogonal_projector_power
    {A ι : Type*} [Ring A] [Fintype ι] [DecidableEq ι] [Algebra ℂ A]
    (P : ι → A)
    (hidem : ∀ i, P i * P i = P i)
    (hortho : ∀ i j, i ≠ j → P i * P j = 0)
    (hsum : (∑ i, P i) = 1)
    (ε : ι → ℂ) (k : ℕ) :
    (∑ i, ε i • P i) ^ k = ∑ i, (ε i ^ k) • P i := by
  induction k with
  | zero =>
      rw [pow_zero, ← hsum]
      refine Finset.sum_congr rfl ?_
      intro i _
      simp
  | succ k ih =>
      rw [pow_succ', ih, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [mul_smul_comm]
      have hmul : (∑ j, ε j • P j) * P i = ε i • P i := by
        rw [Finset.sum_mul]
        have hterm : ∀ j, (ε j • P j) * P i = (if j = i then ε i • P i else 0) := by
          intro j
          by_cases hji : j = i
          · subst j
            simp [hidem i]
          · simp [hortho j i hji, hji]
        rw [Finset.sum_congr rfl (fun j _ => hterm j)]
        simp
      rw [hmul, smul_smul, pow_succ]


end InfoGeometry.Canonical.ExplicitWitnessObligations
