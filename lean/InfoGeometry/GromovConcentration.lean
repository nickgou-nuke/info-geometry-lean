import Mathlib.Data.Nat.Choose.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Finite Pascal counting atoms for Gromov concentration

This module states Pascal-row facts directly with mathlib's canonical binomial
coefficients `Nat.choose` and row-sum lemma `Nat.sum_range_choose`.

No custom binomial wrapper, Stirling approximation, asymptotic concentration
theorem, median dominance theorem, Lévy-family result, or analytic limit is
asserted.
-/

set_option autoImplicit false

namespace InfoGeometry.GromovConcentration

open scoped BigOperators

/-- Reflective symmetry of finite Pascal multiplicities. -/
theorem gromov_pascal_symmetry (n : ℕ) :
    ∀ k : ℕ, k ≤ n → Nat.choose n k = Nat.choose n (n - k) := by
  intro k hk
  exact (Nat.choose_symm hk).symm

/-- The row sum of finite Pascal multiplicities is the Boolean state count `2^n`. -/
theorem gromov_row_sum (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), Nat.choose n k) = 2 ^ n := by
  exact Nat.sum_range_choose n

/--
The inductive row-sum step: adjoining one binary coordinate doubles the finite
unnormalized state count.
-/
theorem gromov_row_sum_step (n : ℕ) (S : ℕ → ℕ)
    (h_sum : ∀ j, S j = ∑ k ∈ Finset.range (j + 1), Nat.choose j k) :
    S (n + 1) = 2 * S n := by
  rw [h_sum (n + 1), h_sum n, gromov_row_sum (n + 1), gromov_row_sum n]
  rw [pow_succ]
  ring

end InfoGeometry.GromovConcentration
