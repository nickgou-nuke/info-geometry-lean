/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Arithmetic.PrimeDistributionLaw

/-!
# Finite smoothed von Mangoldt sums

This file studies the integer-cutoff specialization of the real arithmetic
statistic `∑ n ≤ X, Λ(n) * (X / n - 1)₊` appearing in item 5 of
<https://alpo.ge/remark.pdf> (accessed 2026-11-20).

The existing native von Mangoldt weights and Chebyshev sum are reused. The
zero index contributes zero because `Λ(0) = 0`; no division by a positive
index is cancelled without proving that index is nonzero.

The first difference is a harmonic von Mangoldt sum. Its second difference
recovers the original von Mangoldt weight, so strict discrete convexity occurs
exactly at prime powers. These are finite identities and inequalities over
`ℝ`, with no zero-location, explicit-formula, or asymptotic conclusion.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeDistributionLaw

/-- Harmonic von Mangoldt sum `A(N) = ∑ n ≤ N, Λ(n) / n`. -/
def harmonicMangoldtSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), vonMangoldtWeight n / (n : ℝ)

/-- Integer-cutoff smoothed von Mangoldt sum `S(N) = ∑ n ≤ N, Λ(n)(N/n - 1)`. -/
def smoothedMangoldtSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1),
    vonMangoldtWeight n * ((N : ℝ) / (n : ℝ) - 1)

@[simp] theorem harmonicMangoldtSum_zero : harmonicMangoldtSum 0 = 0 := by
  simp [harmonicMangoldtSum]

@[simp] theorem smoothedMangoldtSum_zero : smoothedMangoldtSum 0 = 0 := by
  simp [smoothedMangoldtSum, vonMangoldtWeight]

@[simp] theorem smoothedMangoldtSum_one : smoothedMangoldtSum 1 = 0 := by
  norm_num [smoothedMangoldtSum, Finset.sum_range_succ, vonMangoldtWeight]

/-- Adding one cutoff adds precisely the next harmonic weight. -/
theorem harmonicMangoldtSum_succ (N : ℕ) :
    harmonicMangoldtSum (N + 1) = harmonicMangoldtSum N +
      vonMangoldtWeight (N + 1) / ((N + 1 : ℕ) : ℝ) := by
  unfold harmonicMangoldtSum
  rw [Finset.sum_range_succ]

/-- Adding one cutoff adds precisely the next von Mangoldt weight to `ψ`. -/
theorem chebyshevPsiFinite_succ (N : ℕ) :
    chebyshevPsiFinite (N + 1) = chebyshevPsiFinite N + vonMangoldtWeight (N + 1) := by
  unfold chebyshevPsiFinite
  rw [Finset.sum_range_succ]

/-- Exact separation of the harmonic part and the existing Chebyshev sum. -/
theorem smoothedMangoldtSum_eq_harmonic_sub_psi (N : ℕ) :
    smoothedMangoldtSum N = (N : ℝ) * harmonicMangoldtSum N -
      chebyshevPsiFinite N := by
  unfold smoothedMangoldtSum harmonicMangoldtSum chebyshevPsiFinite
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  ring

/-- The raw integer-cutoff sum agrees with the positive-part statistic. -/
theorem smoothedMangoldtSum_eq_positivePart (N : ℕ) :
    smoothedMangoldtSum N = ∑ n ∈ Finset.range (N + 1),
      vonMangoldtWeight n * max ((N : ℝ) / (n : ℝ) - 1) 0 := by
  unfold smoothedMangoldtSum
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    simp [vonMangoldtWeight]
  · have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn0
    have hnle : (n : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    have hkernel : 0 ≤ (N : ℝ) / (n : ℝ) - 1 := by
      apply sub_nonneg.mpr
      exact (le_div_iff₀ hnpos).2 (by simpa using hnle)
    rw [max_eq_left hkernel]

theorem harmonicMangoldtSum_nonneg (N : ℕ) : 0 ≤ harmonicMangoldtSum N := by
  unfold harmonicMangoldtSum
  exact Finset.sum_nonneg fun n _hn =>
    div_nonneg (vonMangoldtWeight_nonneg n) (Nat.cast_nonneg n)

theorem smoothedMangoldtSum_nonneg (N : ℕ) : 0 ≤ smoothedMangoldtSum N := by
  rw [smoothedMangoldtSum_eq_positivePart]
  exact Finset.sum_nonneg fun n _hn =>
    mul_nonneg (vonMangoldtWeight_nonneg n) (le_max_right _ _)

/-- The smoothed sum has the harmonic von Mangoldt sum as its first difference. -/
theorem smoothedMangoldtSum_succ_sub (N : ℕ) :
    smoothedMangoldtSum (N + 1) - smoothedMangoldtSum N = harmonicMangoldtSum N := by
  rw [smoothedMangoldtSum_eq_harmonic_sub_psi (N + 1),
    smoothedMangoldtSum_eq_harmonic_sub_psi N,
    harmonicMangoldtSum_succ, chebyshevPsiFinite_succ]
  simp only [Nat.cast_add, Nat.cast_one]
  have hne : (N : ℝ) + 1 ≠ 0 := by positivity
  have hcancel : ((N : ℝ) + 1) *
      (vonMangoldtWeight (N + 1) / ((N : ℝ) + 1)) = vonMangoldtWeight (N + 1) := by
    exact mul_div_cancel₀ _ hne
  nlinarith

/-- Exact second-difference formula, including the boundary `N = 0`. -/
theorem smoothedMangoldtSum_second_difference (N : ℕ) :
    smoothedMangoldtSum (N + 2) - 2 * smoothedMangoldtSum (N + 1) +
      smoothedMangoldtSum N = vonMangoldtWeight (N + 1) / ((N + 1 : ℕ) : ℝ) := by
  have h₀ := smoothedMangoldtSum_succ_sub N
  have h₁ := smoothedMangoldtSum_succ_sub (N + 1)
  have hA := harmonicMangoldtSum_succ N
  have hindex : N + 1 + 1 = N + 2 := by omega
  rw [hindex] at h₁
  linarith

/-- The second difference is nonnegative: a finite discrete convexity statement. -/
theorem smoothedMangoldtSum_second_difference_nonneg (N : ℕ) :
    0 ≤ smoothedMangoldtSum (N + 2) - 2 * smoothedMangoldtSum (N + 1) +
      smoothedMangoldtSum N := by
  rw [smoothedMangoldtSum_second_difference]
  exact div_nonneg (vonMangoldtWeight_nonneg (N + 1)) (Nat.cast_nonneg _)

/-- Strict discrete convexity detects precisely the native prime-power support of `Λ`. -/
theorem smoothedMangoldtSum_second_difference_pos_iff (N : ℕ) :
    0 < smoothedMangoldtSum (N + 2) - 2 * smoothedMangoldtSum (N + 1) +
      smoothedMangoldtSum N ↔ IsPrimePow (N + 1) := by
  rw [smoothedMangoldtSum_second_difference]
  have hpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  rw [div_pos_iff_of_pos_right hpos]
  exact ArithmeticFunction.vonMangoldt_pos_iff

/-- The smoothing retains the original arithmetic data: multiplication recovers `Λ(N+1)`. -/
theorem vonMangoldtWeight_eq_mul_second_difference (N : ℕ) :
    vonMangoldtWeight (N + 1) = ((N + 1 : ℕ) : ℝ) *
      (smoothedMangoldtSum (N + 2) - 2 * smoothedMangoldtSum (N + 1) +
        smoothedMangoldtSum N) := by
  rw [smoothedMangoldtSum_second_difference]
  have hne : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  exact (mul_div_cancel₀ _ hne).symm

theorem harmonicMangoldtSum_monotone : Monotone harmonicMangoldtSum := by
  apply monotone_nat_of_le_succ
  intro N
  rw [harmonicMangoldtSum_succ]
  exact le_add_of_nonneg_right
    (div_nonneg (vonMangoldtWeight_nonneg (N + 1)) (Nat.cast_nonneg _))

theorem smoothedMangoldtSum_monotone : Monotone smoothedMangoldtSum := by
  apply monotone_nat_of_le_succ
  intro N
  have h := smoothedMangoldtSum_succ_sub N
  have hnonneg := harmonicMangoldtSum_nonneg N
  linarith

end InfoGeometry.Arithmetic.PrimeDistributionLaw

end
