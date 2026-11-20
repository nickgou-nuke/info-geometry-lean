/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quantitative interpolation bounds for `x * log x`

The chord error of `x * log x` is nonnegative on the nonnegative real axis.
On `[a,b]`, with `0 < a ≤ b`, its second derivative is bounded above by `1/a`.
Subtracting it from `x² / (2a)` gives a convex function and hence the quantitative
quadratic upper bound for the chord error. On a unit interval this is
`t(1-t)/(2a) ≤ 1/(8a)`.

All results are ordinary real calculus. No arithmetic asymptotic estimate or
zero-free region is assumed or obtained in this owner.
-/

noncomputable section

namespace InfoGeometry.Analysis.MulLogInterpolation

open Set

/-- The linear-interpolation error for the convex function `x * log x`. -/
def mulLogInterpolationError (a b t : ℝ) : ℝ :=
  (1 - t) * (a * Real.log a) + t * (b * Real.log b) -
    ((1 - t) * a + t * b) * Real.log ((1 - t) * a + t * b)

@[simp] theorem mulLogInterpolationError_zero (a b : ℝ) :
    mulLogInterpolationError a b 0 = 0 := by
  simp [mulLogInterpolationError]

@[simp] theorem mulLogInterpolationError_one (a b : ℝ) :
    mulLogInterpolationError a b 1 = 0 := by
  simp [mulLogInterpolationError]

/-- Native convexity supplies the lower error bound, including the endpoint zero. -/
theorem mulLogInterpolationError_nonneg {a b t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ mulLogInterpolationError a b t := by
  apply sub_nonneg.mpr
  simpa only [smul_eq_mul] using
    Real.convexOn_mul_log.2 ha hb (sub_nonneg.mpr ht1) ht0 (by ring)

/-- Strict convexity detects every interior interpolation between distinct points. -/
theorem mulLogInterpolationError_pos {a b t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≠ b) (ht0 : 0 < t) (ht1 : t < 1) :
    0 < mulLogInterpolationError a b t := by
  apply sub_pos.mpr
  simpa only [smul_eq_mul] using
    Real.strictConvexOn_mul_log.2 ha hb hab (sub_pos.mpr ht1) ht0 (by ring)

/-- The quadratic with curvature `1/a` dominates the curvature of `x * log x`
for every `x ≥ a > 0`. -/
theorem convexOn_quadratic_sub_mul_log {a : ℝ} (ha : 0 < a) :
    ConvexOn ℝ (Ici a) (fun x : ℝ => x ^ 2 / (2 * a) - x * Real.log x) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg
    (f' := fun x : ℝ => (2 * x) / (2 * a) - (Real.log x + 1))
    (f'' := fun x : ℝ => 2 / (2 * a) - x⁻¹) (convex_Ici a)
  · exact (((continuous_id.pow 2).div_const (2 * a)).sub
      Real.continuous_mul_log).continuousOn
  · intro x hx
    have hax : a < x := by
      simpa only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] using hx
    have hxp : 0 < x := ha.trans hax
    have hd : HasDerivAt (fun x : ℝ => x ^ 2 / (2 * a) - x * Real.log x)
        ((2 * x) / (2 * a) - (Real.log x + 1)) x := by
      simpa using! ((hasDerivAt_pow 2 x).div_const (2 * a)).sub
        (Real.hasDerivAt_mul_log hxp.ne')
    exact hd.hasDerivWithinAt
  · intro x hx
    have hax : a < x := by
      simpa only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] using hx
    have hxp : 0 < x := ha.trans hax
    have hd : HasDerivAt (fun x : ℝ => (2 * x) / (2 * a) - (Real.log x + 1))
        (2 / (2 * a) - x⁻¹) x := by
      simpa using! (((hasDerivAt_id x).const_mul 2).div_const (2 * a)).sub
        ((Real.hasDerivAt_log hxp.ne').add_const 1)
    exact hd.hasDerivWithinAt
  · intro x hx
    have hax : a < x := by
      simpa only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] using hx
    have htwo : (2 : ℝ) / (2 * a) = a⁻¹ := by
      rw [div_mul_eq_div_div]
      norm_num [one_div]
    rw [htwo]
    exact sub_nonneg.mpr (inv_anti₀ ha hax.le)

/-- The error bound on an arbitrary interval, with an explicit quadratic constant. -/
theorem mulLogInterpolationError_le_quadratic {a b t : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    mulLogInterpolationError a b t ≤ t * (1 - t) * (b - a) ^ 2 / (2 * a) := by
  let q : ℝ → ℝ := fun x => x ^ 2 / (2 * a) - x * Real.log x
  have hq : q ((1 - t) * a + t * b) ≤ (1 - t) * q a + t * q b := by
    simpa only [smul_eq_mul] using
      (convexOn_quadratic_sub_mul_log ha).2 (show a ∈ Ici a by simp)
        (show b ∈ Ici a from hab) (sub_nonneg.mpr ht1) ht0 (by ring)
  have hquadratic : (1 - t) * (a ^ 2 / (2 * a)) + t * (b ^ 2 / (2 * a)) -
      ((1 - t) * a + t * b) ^ 2 / (2 * a) =
        t * (1 - t) * (b - a) ^ 2 / (2 * a) := by
    ring
  calc
    mulLogInterpolationError a b t =
        ((1 - t) * (a ^ 2 / (2 * a)) + t * (b ^ 2 / (2 * a)) -
          ((1 - t) * a + t * b) ^ 2 / (2 * a)) -
        ((1 - t) * q a + t * q b - q ((1 - t) * a + t * b)) := by
          dsimp [mulLogInterpolationError, q]
          ring
    _ ≤ (1 - t) * (a ^ 2 / (2 * a)) + t * (b ^ 2 / (2 * a)) -
          ((1 - t) * a + t * b) ^ 2 / (2 * a) := by linarith
    _ = t * (1 - t) * (b - a) ^ 2 / (2 * a) := hquadratic

/-- On a unit interval the exact bound is `t(1-t)/(2a)`. -/
theorem mulLogInterpolationError_unit_bounds {a t : ℝ}
    (ha : 0 < a) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ mulLogInterpolationError a (a + 1) t ∧
      mulLogInterpolationError a (a + 1) t ≤ t * (1 - t) / (2 * a) := by
  refine ⟨mulLogInterpolationError_nonneg ha.le (by linarith) ht0 ht1, ?_⟩
  simpa using mulLogInterpolationError_le_quadratic ha (by linarith : a ≤ a + 1) ht0 ht1

/-- Maximizing the quadratic factor gives the uniform unit-interval bound. -/
theorem mulLogInterpolationError_unit_le {a t : ℝ}
    (ha : 0 < a) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    mulLogInterpolationError a (a + 1) t ≤ 1 / (8 * a) := by
  have hshape : t * (1 - t) ≤ (1 : ℝ) / 4 := by
    nlinarith [sq_nonneg (t - 1 / 2)]
  calc
    mulLogInterpolationError a (a + 1) t ≤ t * (1 - t) / (2 * a) :=
      (mulLogInterpolationError_unit_bounds ha ht0 ht1).2
    _ ≤ (1 / 4 : ℝ) / (2 * a) :=
      (div_le_div_iff_of_pos_right (by positivity : 0 < 2 * a)).mpr hshape
    _ = 1 / (8 * a) := by ring

/-- The smooth centering term has strictly positive unit second differences. -/
theorem mulLog_second_difference_pos {a : ℝ} (ha : 0 ≤ a) :
    0 < (a + 2) * Real.log (a + 2) - 2 * ((a + 1) * Real.log (a + 1)) +
      a * Real.log a := by
  have h := mulLogInterpolationError_pos ha (by linarith : 0 ≤ a + 2)
    (by linarith : a ≠ a + 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hmid : (1 - (1 / 2 : ℝ)) * a + (1 / 2 : ℝ) * (a + 2) = a + 1 := by ring
  dsimp [mulLogInterpolationError] at h
  rw [hmid] at h
  linarith

end InfoGeometry.Analysis.MulLogInterpolation

end
