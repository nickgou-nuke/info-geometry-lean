/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Analysis.SmoothedMellinKernel
import InfoGeometry.Arithmetic.CenteredSmoothedMangoldt
import Mathlib.Basic.Complex.BigOperators

/-!
# Finite Mellin integrals for actual von Mangoldt smoothing

The finite positive-part truncation below uses the existing native von Mangoldt
weight. Once its truncation reaches the natural floor of a nonnegative real
cutoff, it agrees exactly with `smoothedMangoldtReal`.

For `1 < s.re`, each weighted ramp is absolutely integrable on `(1, ∞)`.
Finite linearity of the integral therefore identifies the truncated smoothing
transform with a finite von Mangoldt Dirichlet polynomial divided by
`s * (s - 1)`. The zero index is handled by `vonMangoldtWeight 0 = 0`.
This file does not exchange an infinite series with an integral.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open InfoGeometry.Analysis.SmoothedMellinKernel

namespace InfoGeometry.Arithmetic.PrimeDistributionLaw

/-- A finite ramp truncation of the actual smoothed arithmetic statistic. -/
def smoothedMangoldtTruncation (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1),
    vonMangoldtWeight n * max (x / (n : ℝ) - 1) 0

/-- At the matching integer cutoff, the truncation is the existing finite sum. -/
@[simp] theorem smoothedMangoldtTruncation_natCast (N : ℕ) :
    smoothedMangoldtTruncation N (N : ℝ) = smoothedMangoldtSum N := by
  exact (smoothedMangoldtSum_eq_positivePart N).symm

/-- Once all possible nonzero ramp terms are included, the truncation agrees
with the existing real-cutoff sum. -/
theorem smoothedMangoldtTruncation_eq_real (N : ℕ) {x : ℝ}
    (hx : 0 ≤ x) (hN : ⌊x⌋₊ ≤ N) :
    smoothedMangoldtTruncation N x = smoothedMangoldtReal x := by
  unfold smoothedMangoldtTruncation smoothedMangoldtReal
  calc
    (∑ n ∈ Finset.range (N + 1), vonMangoldtWeight n * max (x / (n : ℝ) - 1) 0) =
        ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
          vonMangoldtWeight n * max (x / (n : ℝ) - 1) 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hN 1))
      intro n _hn hn
      have hnFloor : ⌊x⌋₊ + 1 ≤ n := by
        simpa only [Finset.mem_range, not_lt] using hn
      have hxlt : x < (n : ℝ) := by
        apply (Nat.lt_floor_add_one x).trans_le
        exact_mod_cast hnFloor
      have hnpos : 0 < (n : ℝ) := hx.trans_lt hxlt
      have hratio : x / (n : ℝ) - 1 ≤ 0 :=
        sub_nonpos.mpr ((div_le_iff₀ hnpos).mpr (by simpa using hxlt.le))
      rw [max_eq_right hratio, mul_zero]
    _ = ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
          vonMangoldtWeight n * (x / (n : ℝ) - 1) := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hn0 : n = 0
      · subst n
        simp [vonMangoldtWeight]
      · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
        have hnle : (n : ℝ) ≤ x := by
          apply le_trans _ (Nat.floor_le hx)
          exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hn)
        have hratio : 0 ≤ x / (n : ℝ) - 1 :=
          sub_nonneg.mpr ((le_div_iff₀ hnpos).mpr (by simpa using hnle))
        rw [max_eq_left hratio]

/-- The weighted truncation is exactly the finite sum of the native ramp kernels. -/
theorem smoothedMangoldtTruncation_mellinIntegrand (N : ℕ) (s : ℂ) (x : ℝ) :
    (smoothedMangoldtTruncation N x : ℂ) * (x : ℂ) ^ (-s - 1) =
      ∑ n ∈ Finset.range (N + 1),
        (vonMangoldtWeight n : ℂ) * rampMellinIntegrand (n : ℝ) s x := by
  simp only [smoothedMangoldtTruncation, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.sum_mul, rampMellinIntegrand, mul_assoc]

/-- A single actual von Mangoldt coefficient times its ramp is integrable,
including the zero coefficient at index zero. -/
theorem integrableOn_vonMangoldt_ramp (n : ℕ) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn
      (fun x : ℝ => (vonMangoldtWeight n : ℂ) * rampMellinIntegrand (n : ℝ) s x)
      (Ioi 1) := by
  by_cases hn0 : n = 0
  · subst n
    simp [vonMangoldtWeight]
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
    exact (integrableOn_Ioi_one_rampMellinIntegrand hn1 hs).const_mul _

/-- Absolute integrability of the actual finite arithmetic smoothing transform. -/
theorem integrableOn_smoothedMangoldtTruncation (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn
      (fun x : ℝ => (smoothedMangoldtTruncation N x : ℂ) * (x : ℂ) ^ (-s - 1))
      (Ioi 1) := by
  simp_rw [smoothedMangoldtTruncation_mellinIntegrand]
  exact integrable_finsetSum (Finset.range (N + 1))
    (fun n _hn => integrableOn_vonMangoldt_ramp n hs)

/-- Finite Mellin identity for actual von Mangoldt coefficients. -/
theorem integral_smoothedMangoldtTruncation (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    (∫ x : ℝ in Ioi 1,
      (smoothedMangoldtTruncation N x : ℂ) * (x : ℂ) ^ (-s - 1)) =
      (∑ n ∈ Finset.range (N + 1), (vonMangoldtWeight n : ℂ) * (n : ℂ) ^ (-s)) /
        (s * (s - 1)) := by
  simp_rw [smoothedMangoldtTruncation_mellinIntegrand]
  rw [integral_finsetSum (Finset.range (N + 1))
    (fun n _hn => integrableOn_vonMangoldt_ramp n hs), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases hn0 : n = 0
  · subst n
    simp [vonMangoldtWeight]
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
    rw [integral_const_mul, integral_Ioi_one_rampMellinIntegrand hn1 hs]
    simp only [Complex.ofReal_natCast, mul_div_assoc]

end InfoGeometry.Arithmetic.PrimeDistributionLaw
