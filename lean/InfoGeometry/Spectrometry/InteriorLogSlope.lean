/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Finite-sum identities for interior spectral log slopes

Rows represent spectral lines and columns represent the
same selected interior samples for every line. The weights and predictor are
also shared between lines.

`weightedSlope` is the usual weighted least-squares coefficient formula when
weights are nonnegative, their sum is positive, and the centered predictor has
positive squared norm. This file proves algebraic identities of that formula;
it does not prove an optimization or statistical inference theorem.

The identities are unconditional when division is used only algebraically.
Nonzero weight mass is explicit for removal of constants, and a nonzero
predictor denominator is explicit for recovery of an affine slope.
-/

namespace InfoGeometry.Spectrometry.InteriorLogSlope

open scoped BigOperators

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def weightedMean (w x : J → ℝ) : ℝ :=
  (∑ j, w j * x j) / ∑ j, w j

def slopeDenominator (w x : J → ℝ) : ℝ :=
  ∑ j, w j * (x j - weightedMean w x) ^ 2

def weightedSlope (w x y : J → ℝ) : ℝ :=
  (∑ j, w j * (x j - weightedMean w x) * y j) / slopeDenominator w x

theorem weightedSlope_add (w x y z : J → ℝ) :
    weightedSlope w x (fun j => y j + z j) =
      weightedSlope w x y + weightedSlope w x z := by
  simp only [weightedSlope, mul_add, Finset.sum_add_distrib, add_div]

theorem weightedSlope_mul (w x y : J → ℝ) (a : ℝ) :
    weightedSlope w x (fun j => a * y j) = a * weightedSlope w x y := by
  unfold weightedSlope
  have hsum :
      (∑ j, w j * (x j - weightedMean w x) * (a * y j)) =
        a * ∑ j, w j * (x j - weightedMean w x) * y j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  ring

/-- Fixed linear combinations over lines commute with a common slope operator.
Different sample subsets or different per-line weights are not covered. -/
theorem weightedSlope_line_combination
    (w x : J → ℝ) (lineWeights : I → ℝ) (L : I → J → ℝ) :
    weightedSlope w x (fun j => ∑ i, lineWeights i * L i j) =
      ∑ i, lineWeights i * weightedSlope w x (L i) := by
  simp only [weightedSlope, Finset.mul_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The log of the geometric sample factor is the mean of the line logs. -/
def sampleLogMean (L : I → J → ℝ) : J → ℝ :=
  fun j => (∑ i, L i j) / Fintype.card I

/-- Consequently its slope is the arithmetic mean of the per-line log slopes. -/
theorem weightedSlope_sampleLogMean (w x : J → ℝ) (L : I → J → ℝ) :
    weightedSlope w x (sampleLogMean L) =
      (∑ i, weightedSlope w x (L i)) / Fintype.card I := by
  have hmean : sampleLogMean L =
      fun j => ∑ i, (Fintype.card I : ℝ)⁻¹ * L i j := by
    funext j
    unfold sampleLogMean
    rw [← Finset.mul_sum]
    ring
  rw [hmean, weightedSlope_line_combination, ← Finset.mul_sum]
  ring

theorem sum_weighted_centered (w x : J → ℝ) (hw : (∑ j, w j) ≠ 0) :
    ∑ j, w j * (x j - weightedMean w x) = 0 := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, weightedMean]
  field_simp [hw] <;> ring

theorem weightedSlope_const (w x : J → ℝ) (hw : (∑ j, w j) ≠ 0) (a : ℝ) :
    weightedSlope w x (fun _ => a) = 0 := by
  unfold weightedSlope
  rw [← Finset.sum_mul, sum_weighted_centered w x hw]
  simp

/-- A line-response correction changes a log intercept, not the fitted slope. -/
theorem weightedSlope_add_constant
    (w x y : J → ℝ) (hw : (∑ j, w j) ≠ 0) (a : ℝ) :
    weightedSlope w x (fun j => a + y j) = weightedSlope w x y := by
  rw [weightedSlope_add, weightedSlope_const w x hw, zero_add]

theorem weightedSlope_predictor (w x : J → ℝ)
    (hw : (∑ j, w j) ≠ 0) (hd : slopeDenominator w x ≠ 0) :
    weightedSlope w x x = 1 := by
  have hterm (j : J) :
      w j * (x j - weightedMean w x) * x j =
        w j * (x j - weightedMean w x) ^ 2 +
          weightedMean w x * (w j * (x j - weightedMean w x)) := by ring
  unfold weightedSlope
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_weighted_centered w x hw]
  simp only [mul_zero, add_zero]
  exact div_self hd

theorem weightedSlope_affine_predictor (w x : J → ℝ)
    (hw : (∑ j, w j) ≠ 0) (hd : slopeDenominator w x ≠ 0) (a b : ℝ) :
    weightedSlope w x (fun j => a + b * x j) = b := by
  rw [weightedSlope_add_constant w x _ hw, weightedSlope_mul,
    weightedSlope_predictor w x hw hd, mul_one]

/-- A common exponential point correction adds the same time/predictor slope
term to every line. It need not preserve the spatial slope. -/
theorem weightedSlope_common_log_correction
    (w x y time : J → ℝ) (lambda : ℝ) :
    weightedSlope w x (fun j => y j + lambda * time j) =
      weightedSlope w x y + lambda * weightedSlope w x time := by
  rw [weightedSlope_add, weightedSlope_mul]

theorem weightedSlope_exponential_correction
    (w x intensity time : J → ℝ) (lambda : ℝ)
    (hpos : ∀ j, 0 < intensity j) :
    weightedSlope w x (fun j => Real.log (intensity j * Real.exp (lambda * time j))) =
      weightedSlope w x (fun j => Real.log (intensity j)) +
        lambda * weightedSlope w x time := by
  simp_rw [Real.log_mul (hpos _).ne' (Real.exp_ne_zero _), Real.log_exp]
  exact weightedSlope_common_log_correction w x _ time lambda

/-- If acquisition time is affine in position, its correction is indistinguishable
from a slope change in this log-linear observation model. -/
theorem weightedSlope_affine_time_correction
    (w x y : J → ℝ) (hw : (∑ j, w j) ≠ 0)
    (hd : slopeDenominator w x ≠ 0) (lambda t₀ tau : ℝ) :
    weightedSlope w x (fun j => y j + lambda * (t₀ + tau * x j)) =
      weightedSlope w x y + lambda * tau := by
  rw [weightedSlope_common_log_correction,
    weightedSlope_affine_predictor w x hw hd]

/-- Arbitrary common column gains cannot change differences of line slopes. -/
theorem slope_difference_common_correction (w x y z correction : J → ℝ) :
    weightedSlope w x (fun j => y j + correction j) -
      weightedSlope w x (fun j => z j + correction j) =
        weightedSlope w x y - weightedSlope w x z := by
  rw [weightedSlope_add, weightedSlope_add]
  ring

/-- Opposite line-specific deviations cancel exactly in the geometric mean.
Hence an affine mean does not establish that either line is affine. -/
theorem opposite_deviations_geometric_mean
    (a b mu position deviation : ℝ) :
    Real.exp (((a - mu * position + deviation) +
      (b - mu * position - deviation)) / 2) =
        Real.exp ((a + b) / 2) * Real.exp (-mu * position) := by
  rw [← Real.exp_add]
  congr 1
  ring

end
end InfoGeometry.Spectrometry.InteriorLogSlope
