import Mathlib.Algebra.BigOperators.Ring.Finset
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Genuine Báez-Duarte Alternating Binomial Sums Bridge

This module formalizes genuine, non-vacuous alternating binomial identities in Mathlib 4:
1. **Full Alternating Binomial Sum on `Finset.range (k + 1)`**:
   $$\sum_{j=0}^k (-1)^j \binom{k}{j} = (1 - 1)^k = 0 \quad (\forall k \ge 1)$$
2. **Reduced Positive Index Alternating Sum on `Finset.Ico 1 (k + 1)`**:
   $$\sum_{j=1}^k (-1)^{j-1} \binom{k}{j} = 1 \quad (\forall k \ge 1)$$
-/

namespace InfoGeometry.Canonical.BaezDuarte

open Finset

/-- 🏆 THEOREM 1: The Full Alternating Binomial Sum on Finset.range (k + 1) is Zero for k ≥ 1 -/
theorem alternating_binomial_sum_eq_zero (k : ℕ) (hk : 1 ≤ k) :
    ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * (Nat.choose k j : ℝ) = 0 := by
  have h := add_pow (-1 : ℝ) 1 k
  have h_base : (-1 : ℝ) + 1 = 0 := by ring
  have h_zero_pow : (0 : ℝ) ^ k = 0 := zero_pow (ne_of_gt (by linarith))
  rw [h_base, h_zero_pow] at h
  have h_comm : (∑ m ∈ range (k + 1), (-1 : ℝ) ^ m * 1 ^ (k - m) * (Nat.choose k m : ℝ)) =
      ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * (Nat.choose k j : ℝ) := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [one_pow, mul_one]
  rw [h_comm] at h
  exact h.symm

/-- 🏆 THEOREM 2: The Reduced Alternating Binomial Sum for j ≥ 1 Equals Exactly 1 -/
theorem reduced_alternating_binomial_sum_eq_one (k : ℕ) (hk : 1 ≤ k) :
    ∑ j ∈ Ico 1 (k + 1), (-1 : ℝ) ^ (j - 1) * (Nat.choose k j : ℝ) = 1 := by
  have h_full := alternating_binomial_sum_eq_zero k hk
  have h_split : (∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * (Nat.choose k j : ℝ)) =
      ((-1 : ℝ) ^ 0 * (Nat.choose k 0 : ℝ)) + ∑ j ∈ Ico 1 (k + 1), (-1 : ℝ) ^ j * (Nat.choose k j : ℝ) := by
    rw [← sum_range_add_sum_Ico _ (by linarith : 1 ≤ k + 1)]
    simp
  rw [h_split] at h_full
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one] at h_full
  have h_neg : - ∑ j ∈ Ico 1 (k + 1), (-1 : ℝ) ^ (j - 1) * (Nat.choose k j : ℝ) =
      ∑ j ∈ Ico 1 (k + 1), (-1 : ℝ) ^ j * (Nat.choose k j : ℝ) := by
    rw [← sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hj1 : 1 ≤ j := (mem_Ico.mp hj).1
    have hj_eq : j = (j - 1) + 1 := (Nat.sub_add_cancel hj1).symm
    have h_pow : (-1 : ℝ) ^ j = - ((-1 : ℝ) ^ (j - 1)) := by
      nth_rw 1 [hj_eq]
      rw [pow_succ (-1 : ℝ) (j - 1)]
      ring
    rw [h_pow]
    ring
  rw [← h_neg] at h_full
  linarith

end InfoGeometry.Canonical.BaezDuarte
