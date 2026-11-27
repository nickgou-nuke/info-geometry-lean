/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Arithmetic.FiniteSmoothedMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Real-cutoff Mangoldt smoothing

The floor-indexed real statistic agrees with the existing finite owner at
natural cutoffs. Its interpolation on each closed unit interval is exactly
affine, including the endpoint where the new summand has zero weight.
Centering uses Mathlib's actual Euler constant. No asymptotic estimate or
zeta zero exclusion is assumed or concluded here.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeDistributionLaw

/-- Real-cutoff version of the existing finite smoothed von Mangoldt sum. -/
def realSmoothedMangoldtSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
    vonMangoldtWeight n * (x / (n : ℝ) - 1)

/-- The centered arithmetic remainder, with the native Euler constant. -/
def centeredSmoothedMangoldtSum (x : ℝ) : ℝ :=
  realSmoothedMangoldtSum x - x * Real.log x +
    (1 + Real.eulerMascheroniConstant) * x

/-- Removing the zero term gives the positive-index floor formula. -/
theorem realSmoothedMangoldtSum_eq_Icc (x : ℝ) :
    realSmoothedMangoldtSum x =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldtWeight n * (x / (n : ℝ) - 1) := by
  have hzero : vonMangoldtWeight 0 * (x / (0 : ℝ) - 1) = 0 := by
    simp [vonMangoldtWeight]
  have herase := Finset.sum_erase
    (s := Finset.range (⌊x⌋₊ + 1))
    (f := fun n => vonMangoldtWeight n * (x / (n : ℝ) - 1))
    (a := 0) (by simpa using hzero)
  have hset : (Finset.range (⌊x⌋₊ + 1)).erase 0 = Finset.Icc 1 ⌊x⌋₊ := by
    ext n
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc, Nat.lt_succ_iff]
    omega
  unfold realSmoothedMangoldtSum
  rw [← hset, ← herase]

@[simp] theorem realSmoothedMangoldtSum_natCast (N : ℕ) :
    realSmoothedMangoldtSum (N : ℝ) = smoothedMangoldtSum N := by
  simp [realSmoothedMangoldtSum, smoothedMangoldtSum]

/-- The same harmonic/Chebyshev separation holds at a real cutoff. -/
theorem realSmoothedMangoldtSum_eq_harmonic_sub_psi (x : ℝ) :
    realSmoothedMangoldtSum x =
      x * harmonicMangoldtSum ⌊x⌋₊ - chebyshevPsiFinite ⌊x⌋₊ := by
  unfold realSmoothedMangoldtSum harmonicMangoldtSum chebyshevPsiFinite
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  ring

/-- Exact affine readout from the integer immediately below the cutoff. -/
theorem realSmoothedMangoldtSum_eq_floor_affine (x : ℝ) :
    realSmoothedMangoldtSum x = smoothedMangoldtSum ⌊x⌋₊ +
      (x - (⌊x⌋₊ : ℝ)) * harmonicMangoldtSum ⌊x⌋₊ := by
  rw [realSmoothedMangoldtSum_eq_harmonic_sub_psi,
    smoothedMangoldtSum_eq_harmonic_sub_psi]
  ring

/-- Affine interpolation includes both ends of the unit interval. -/
theorem realSmoothedMangoldtSum_add_unitInterval (N : ℕ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    realSmoothedMangoldtSum ((N : ℝ) + t) =
      smoothedMangoldtSum N + t * harmonicMangoldtSum N := by
  rcases lt_or_eq_of_le ht1 with htlt | rfl
  · have hfloor : ⌊(N : ℝ) + t⌋₊ = N := by
      apply (Nat.floor_eq_iff (add_nonneg (Nat.cast_nonneg N) ht0)).2
      constructor <;> linarith
    rw [realSmoothedMangoldtSum_eq_floor_affine, hfloor]
    ring
  · rw [show (N : ℝ) + 1 = ((N + 1 : ℕ) : ℝ) by simp,
      realSmoothedMangoldtSum_natCast, one_mul]
    linarith [smoothedMangoldtSum_succ_sub N]

/-- The continuous cutoff is the affine interpolant of the finite sums. -/
theorem realSmoothedMangoldtSum_eq_affine (N : ℕ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    realSmoothedMangoldtSum ((N : ℝ) + t) =
      (1 - t) * smoothedMangoldtSum N + t * smoothedMangoldtSum (N + 1) := by
  rw [realSmoothedMangoldtSum_add_unitInterval N t ht0 ht1]
  have hsucc : smoothedMangoldtSum (N + 1) =
      smoothedMangoldtSum N + harmonicMangoldtSum N := by
    linarith [smoothedMangoldtSum_succ_sub N]
  rw [hsucc]
  ring

/-- Every positive-index kernel in the finite support is nonnegative. -/
theorem realSmoothedMangoldtSum_nonneg (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ realSmoothedMangoldtSum x := by
  rw [realSmoothedMangoldtSum_eq_Icc]
  apply Finset.sum_nonneg
  intro n hn
  have hn' := Finset.mem_Icc.mp hn
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (Nat.zero_lt_one.trans_le hn'.1)
  have hnx : (n : ℝ) ≤ x :=
    (Nat.cast_le.mpr hn'.2).trans (Nat.floor_le hx)
  apply mul_nonneg (vonMangoldtWeight_nonneg n)
  exact sub_nonneg.mpr ((le_div_iff₀ hnpos).2 (by simpa using hnx))

@[simp] theorem centeredSmoothedMangoldtSum_natCast (N : ℕ) :
    centeredSmoothedMangoldtSum (N : ℝ) =
      smoothedMangoldtSum N - (N : ℝ) * Real.log N +
        (1 + Real.eulerMascheroniConstant) * N := by
  simp [centeredSmoothedMangoldtSum]

end InfoGeometry.Arithmetic.PrimeDistributionLaw
