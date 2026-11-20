/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Arithmetic.FiniteSmoothedMangoldt
import InfoGeometry.Analysis.MulLogInterpolation
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Real cutoffs and centered von Mangoldt smoothing

The actual finite Mangoldt sum is affine between successive integer cutoffs.
After subtracting `x * log x` and adding the Euler--Mascheroni linear term,
its interpolation error is exactly the chord error owned by
`Analysis.MulLogInterpolation`. This gives a quantitative transfer of eventual
one-sided power bounds from integers to reals, with the sign fixed throughout.

The transfer does not establish the arithmetic bound. The centered second
difference is strictly negative at every non-prime-power index, so the
uncentered convexity theorem cannot supply such a bound by itself.
-/

noncomputable section

open scoped BigOperators
open InfoGeometry.Analysis.MulLogInterpolation

namespace InfoGeometry.Arithmetic.PrimeDistributionLaw

/-- The existing smoothed arithmetic sum at a real cutoff. The zero coefficient
vanishes, including when the natural floor truncates a negative cutoff to zero. -/
def smoothedMangoldtReal (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
    vonMangoldtWeight n * (x / (n : ℝ) - 1)

/-- The centered statistic, with native Euler--Mascheroni constant. -/
def centeredSmoothedMangoldt (x : ℝ) : ℝ :=
  smoothedMangoldtReal x - x * Real.log x + (1 + Real.eulerMascheroniConstant) * x

@[simp] theorem smoothedMangoldtReal_natCast (N : ℕ) :
    smoothedMangoldtReal (N : ℝ) = smoothedMangoldtSum N := by
  simp [smoothedMangoldtReal, smoothedMangoldtSum]

/-- The same harmonic/Chebyshev decomposition holds at the natural floor. -/
theorem smoothedMangoldtReal_eq_harmonic_sub_psi (x : ℝ) :
    smoothedMangoldtReal x = x * harmonicMangoldtSum ⌊x⌋₊ -
      chebyshevPsiFinite ⌊x⌋₊ := by
  unfold smoothedMangoldtReal harmonicMangoldtSum chebyshevPsiFinite
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  ring

/-- The endpoint at `t = 1` is included: the newly admitted term has zero kernel. -/
theorem smoothedMangoldtReal_add_fraction (N : ℕ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    smoothedMangoldtReal ((N : ℝ) + t) =
      smoothedMangoldtSum N + t * harmonicMangoldtSum N := by
  rcases lt_or_eq_of_le ht1 with ht1 | rfl
  · have hfloor : ⌊(N : ℝ) + t⌋₊ = N := by
      apply (Nat.floor_eq_iff (add_nonneg (Nat.cast_nonneg N) ht0)).2
      constructor <;> linarith
    rw [smoothedMangoldtReal_eq_harmonic_sub_psi, hfloor,
      smoothedMangoldtSum_eq_harmonic_sub_psi]
    ring
  · have h := smoothedMangoldtSum_succ_sub N
    rw [← Nat.cast_add_one, smoothedMangoldtReal_natCast]
    linarith

/-- The real sum is precisely the linear interpolation of the existing integer sum. -/
theorem smoothedMangoldtReal_interpolation (N : ℕ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    smoothedMangoldtReal ((N : ℝ) + t) =
      (1 - t) * smoothedMangoldtSum N + t * smoothedMangoldtSum (N + 1) := by
  rw [smoothedMangoldtReal_add_fraction N ht0 ht1,
    ← smoothedMangoldtSum_succ_sub N]
  ring

/-- Exact centering error; the Euler--Mascheroni linear term cancels. -/
theorem centeredSmoothedMangoldt_interpolation (N : ℕ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    centeredSmoothedMangoldt ((N : ℝ) + t) =
      (1 - t) * centeredSmoothedMangoldt (N : ℝ) +
      t * centeredSmoothedMangoldt ((N + 1 : ℕ) : ℝ) +
      mulLogInterpolationError (N : ℝ) ((N : ℝ) + 1) t := by
  have harg : (1 - t) * (N : ℝ) + t * ((N : ℝ) + 1) = (N : ℝ) + t := by ring
  unfold centeredSmoothedMangoldt
  rw [smoothedMangoldtReal_interpolation N ht0 ht1,
    smoothedMangoldtReal_natCast, smoothedMangoldtReal_natCast]
  simp only [Nat.cast_add, Nat.cast_one, mulLogInterpolationError, harg]
  ring

/-- Quantitative quadratic interpolation bounds for the actual centered statistic. -/
theorem centeredSmoothedMangoldt_interpolation_bounds (N : ℕ) (hN : 1 ≤ N)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let chord := (1 - t) * centeredSmoothedMangoldt (N : ℝ) +
      t * centeredSmoothedMangoldt ((N + 1 : ℕ) : ℝ)
    chord ≤ centeredSmoothedMangoldt ((N : ℝ) + t) ∧
      centeredSmoothedMangoldt ((N : ℝ) + t) ≤ chord + t * (1 - t) / (2 * N) := by
  dsimp only
  rw [centeredSmoothedMangoldt_interpolation N ht0 ht1]
  have hp : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hb := mulLogInterpolationError_unit_bounds hp ht0 ht1
  constructor <;> linarith

/-- The arithmetic and smooth curvatures contribute with opposite signs. -/
theorem centeredSmoothedMangoldt_second_difference (N : ℕ) :
    centeredSmoothedMangoldt ((N + 2 : ℕ) : ℝ) -
      2 * centeredSmoothedMangoldt ((N + 1 : ℕ) : ℝ) +
      centeredSmoothedMangoldt (N : ℝ) =
    vonMangoldtWeight (N + 1) / ((N + 1 : ℕ) : ℝ) -
      (((N : ℝ) + 2) * Real.log ((N : ℝ) + 2) -
        2 * (((N : ℝ) + 1) * Real.log ((N : ℝ) + 1)) + (N : ℝ) * Real.log N) := by
  have h := smoothedMangoldtSum_second_difference N
  unfold centeredSmoothedMangoldt
  rw [smoothedMangoldtReal_natCast, smoothedMangoldtReal_natCast,
    smoothedMangoldtReal_natCast]
  simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] at *
  linarith

/-- In particular the centered statistic is not discretely convex at indices
where the von Mangoldt coefficient vanishes. -/
theorem centeredSmoothedMangoldt_second_difference_neg (N : ℕ)
    (hN : ¬ IsPrimePow (N + 1)) :
    centeredSmoothedMangoldt ((N + 2 : ℕ) : ℝ) -
      2 * centeredSmoothedMangoldt ((N + 1 : ℕ) : ℝ) +
      centeredSmoothedMangoldt (N : ℝ) < 0 := by
  rw [centeredSmoothedMangoldt_second_difference]
  have hz : vonMangoldtWeight (N + 1) = 0 := by
    exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hN
  rw [hz, zero_div, zero_sub]
  exact neg_neg_of_pos (mulLog_second_difference_pos (Nat.cast_nonneg N))

/-- Explicit integer-to-real transfer. The hypothesis `η ≤ 1` includes each
fixed sign `η = 1` and `η = -1`; no absolute bound is inferred from it. -/
theorem centeredSmoothedMangoldt_signed_bound_real
    {η α C : ℝ} (hη : η ≤ 1) (hα : 0 ≤ α) (hC : 0 ≤ C) (N₀ : ℕ)
    (hbound : ∀ N : ℕ, N₀ ≤ N →
      η * centeredSmoothedMangoldt (N : ℝ) ≤ C * (N : ℝ) ^ α)
    {x : ℝ} (hx : ((max N₀ 1 : ℕ) : ℝ) ≤ x) :
    η * centeredSmoothedMangoldt x ≤ (2 ^ α * C + 1 / 8) * x ^ α := by
  have hx1 : 1 ≤ x := by
    have : ((1 : ℕ) : ℝ) ≤ ((max N₀ 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right N₀ 1
    simpa using this.trans hx
  have hx0 : 0 ≤ x := by linarith
  let N : ℕ := ⌊x⌋₊
  let t : ℝ := x - (N : ℝ)
  have hN : max N₀ 1 ≤ N := (Nat.le_floor_iff hx0).2 hx
  have hN0 : N₀ ≤ N := (le_max_left N₀ 1).trans hN
  have hN1 : 1 ≤ N := (le_max_right N₀ 1).trans hN
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0
  have ht0 : 0 ≤ t := sub_nonneg.mpr hNx
  have ht1 : t ≤ 1 := by
    have := Nat.lt_floor_add_one x
    dsimp [t, N]
    linarith
  have hxt : x = (N : ℝ) + t := by dsimp [t]; ring
  have hpowN : (N : ℝ) ^ α ≤ (2 * x) ^ α :=
    Real.rpow_le_rpow (Nat.cast_nonneg N) (by linarith) hα
  have hpowS : ((N + 1 : ℕ) : ℝ) ^ α ≤ (2 * x) ^ α := by
    apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ hα
    simp only [Nat.cast_add, Nat.cast_one]
    linarith
  have hmul : (2 * x) ^ α = 2 ^ α * x ^ α := Real.mul_rpow (by norm_num) hx0
  have hleft : η * centeredSmoothedMangoldt (N : ℝ) ≤ 2 ^ α * C * x ^ α := by
    calc
      _ ≤ C * (N : ℝ) ^ α := hbound N hN0
      _ ≤ C * (2 * x) ^ α := mul_le_mul_of_nonneg_left hpowN hC
      _ = _ := by rw [hmul]; ring
  have hright : η * centeredSmoothedMangoldt ((N + 1 : ℕ) : ℝ) ≤
      2 ^ α * C * x ^ α := by
    calc
      _ ≤ C * ((N + 1 : ℕ) : ℝ) ^ α := hbound (N + 1) (by omega)
      _ ≤ C * (2 * x) ^ α := mul_le_mul_of_nonneg_left hpowS hC
      _ = _ := by rw [hmul]; ring
  have hNp : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN1)
  have hE0 := (mulLogInterpolationError_unit_bounds hNp ht0 ht1).1
  have hE1 := mulLogInterpolationError_unit_le hNp ht0 ht1
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hden : 1 / (8 * (N : ℝ)) ≤ (1 : ℝ) / 8 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  have herr : η * mulLogInterpolationError (N : ℝ) ((N : ℝ) + 1) t ≤
      (1 / 8 : ℝ) * x ^ α := by
    calc
      _ ≤ 1 * mulLogInterpolationError (N : ℝ) ((N : ℝ) + 1) t :=
        mul_le_mul_of_nonneg_right hη hE0
      _ ≤ 1 / (8 * (N : ℝ)) := by simpa using hE1
      _ ≤ (1 : ℝ) / 8 := hden
      _ ≤ (1 / 8 : ℝ) * x ^ α := by nlinarith [Real.one_le_rpow hx1 hα]
  have hl := mul_le_mul_of_nonneg_left hleft (sub_nonneg.mpr ht1)
  have hr := mul_le_mul_of_nonneg_left hright ht0
  rw [hxt, centeredSmoothedMangoldt_interpolation N ht0 ht1]
  rw [← hxt]
  nlinarith

/-- Eventual signed power bounds at integer and real cutoffs are equivalent.
Natural thresholds are cofinal in the real half-line. -/
theorem centeredSmoothedMangoldt_signed_bound_iff
    {η α : ℝ} (hη : η ≤ 1) (hα : 0 ≤ α) :
    (∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      η * centeredSmoothedMangoldt (N : ℝ) ≤ C * (N : ℝ) ^ α) ↔
    (∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ x : ℝ, (N₀ : ℝ) ≤ x →
      η * centeredSmoothedMangoldt x ≤ C * x ^ α) := by
  constructor
  · rintro ⟨C, hC, N₀, hbound⟩
    refine ⟨2 ^ α * C + 1 / 8, by positivity, max N₀ 1, ?_⟩
    exact fun x hx => centeredSmoothedMangoldt_signed_bound_real hη hα hC N₀ hbound hx
  · rintro ⟨C, hC, N₀, hbound⟩
    refine ⟨C, hC, N₀, fun N hN => ?_⟩
    exact hbound (N : ℝ) (by exact_mod_cast hN)

/-- The same sign is retained for every epsilon in a square-root-type bound. -/
theorem centeredSmoothedMangoldt_signed_epsilon_bound_iff
    {η θ : ℝ} (hη : η ≤ 1) (hθ : 0 ≤ θ) :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      η * centeredSmoothedMangoldt (N : ℝ) ≤ C * (N : ℝ) ^ (θ + ε)) ↔
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ x : ℝ, (N₀ : ℝ) ≤ x →
      η * centeredSmoothedMangoldt x ≤ C * x ^ (θ + ε)) := by
  constructor <;> intro h ε hε
  · exact (centeredSmoothedMangoldt_signed_bound_iff hη (by linarith only [hθ, hε])).1 (h ε hε)
  · exact (centeredSmoothedMangoldt_signed_bound_iff hη (by linarith only [hθ, hε])).2 (h ε hε)

end InfoGeometry.Arithmetic.PrimeDistributionLaw

end
