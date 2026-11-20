/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

/-!
# Interpolation error for `x * log x`

On a unit interval with positive left endpoint `a`, the chord of `x * log x`
lies above the function by at most `t * (1 - t) / (2 * a)`, hence at most
`1 / (8 * a)`. The lower bound uses native Mathlib convexity. The upper bound
uses concavity of `x * log x - x^2 / (2 * a)` on `Ici a`, proved from its
explicit first and second derivatives.

These are inequalities for the actual real logarithm. No asymptotic or
zero-location hypothesis is introduced.
-/

noncomputable section

open Set

namespace InfoGeometry.Analysis.CenteredLogInterpolation

/-- The error between the unit-interval chord of `x * log x` and its value. -/
def logChordError (a t : ℝ) : ℝ :=
  (1 - t) * (a * Real.log a) + t * ((a + 1) * Real.log (a + 1)) -
    (a + t) * Real.log (a + t)

/-- Subtracting a quadratic with curvature `1 / a` makes `x * log x` concave
to the right of the positive point `a`. -/
theorem concaveOn_mul_log_sub_quadratic {a : ℝ} (ha : 0 < a) :
    ConcaveOn ℝ (Ici a) (fun x : ℝ => x * Real.log x - x ^ 2 / (2 * a)) := by
  refine concaveOn_of_hasDerivWithinAt2_nonpos
    (f' := fun x : ℝ => Real.log x + 1 - x / a)
    (f'' := fun x : ℝ => x⁻¹ - a⁻¹)
    (convex_Ici a) ?_ ?_ ?_ ?_
  · exact (Real.continuous_mul_log.sub
      ((continuous_id.pow 2).div_const (2 * a))).continuousOn
  · intro x hx
    have hxpos : 0 < x := ha.trans_le (interior_subset hx)
    have hquadratic : HasDerivAt (fun y : ℝ => y ^ 2 / (2 * a)) (x / a) x := by
      convert ((hasDerivAt_id x).pow 2).div_const (2 * a) using 1 <;> norm_num
      all_goals field_simp [ha.ne']
    exact ((Real.hasDerivAt_mul_log hxpos.ne').sub hquadratic).hasDerivWithinAt
  · intro x hx
    have hxpos : 0 < x := ha.trans_le (interior_subset hx)
    have hderiv : HasDerivAt (fun y : ℝ => Real.log y + 1 - y / a)
        (x⁻¹ - a⁻¹) x := by
      simpa only [one_div, Pi.sub_apply, id_eq] using!
        ((Real.hasDerivAt_log hxpos.ne').add_const 1).sub
          ((hasDerivAt_id x).div_const a)
    exact hderiv.hasDerivWithinAt
  · intro x hx
    have hax : a ≤ x := interior_subset hx
    exact sub_nonpos.mpr ((inv_le_inv₀ (ha.trans_le hax) ha).mpr hax)

/-- Convexity gives the nonnegative chord error, including the left endpoint
`a = 0`. -/
theorem logChordError_nonneg {a t : ℝ} (ha : 0 ≤ a)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ logChordError a t := by
  have h := Real.convexOn_mul_log.2
    (show a ∈ Ici (0 : ℝ) from ha)
    (show a + 1 ∈ Ici (0 : ℝ) by simp only [mem_Ici]; linarith)
    (sub_nonneg.mpr ht1) ht0 (by ring : 1 - t + t = 1)
  simp only [smul_eq_mul] at h
  have hpoint : (1 - t) * a + t * (a + 1) = a + t := by ring
  rw [hpoint] at h
  exact sub_nonneg.mpr h

/-- The curvature bound gives the sharper quadratic interpolation error. -/
theorem logChordError_le_quadratic {a t : ℝ} (ha : 0 < a)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    logChordError a t ≤ t * (1 - t) / (2 * a) := by
  have h := (concaveOn_mul_log_sub_quadratic ha).2
    (show a ∈ Ici a by simp)
    (show a + 1 ∈ Ici a by simp only [mem_Ici]; linarith)
    (sub_nonneg.mpr ht1) ht0 (by ring : 1 - t + t = 1)
  simp only [smul_eq_mul] at h
  have hpoint : (1 - t) * a + t * (a + 1) = a + t := by ring
  rw [hpoint] at h
  have herror : logChordError a t - t * (1 - t) / (2 * a) ≤ 0 := by
    calc
      logChordError a t - t * (1 - t) / (2 * a) =
          ((1 - t) * (a * Real.log a - a ^ 2 / (2 * a)) +
            t * ((a + 1) * Real.log (a + 1) - (a + 1) ^ 2 / (2 * a))) -
              ((a + t) * Real.log (a + t) - (a + t) ^ 2 / (2 * a)) := by
        unfold logChordError
        ring
      _ ≤ 0 := sub_nonpos.mpr h
  exact sub_nonpos.mp herror

/-- The quadratic error is at most `1 / (8 * a)`. This estimate holds for
every real `t`; membership in the unit interval is not needed here. -/
theorem quadraticChordBound_le_one_div_eight {a : ℝ} (ha : 0 < a) (t : ℝ) :
    t * (1 - t) / (2 * a) ≤ 1 / (8 * a) := by
  have ht : t * (1 - t) ≤ (1 : ℝ) / 4 := by
    nlinarith [sq_nonneg (t - 1 / 2)]
  calc
    t * (1 - t) / (2 * a) ≤ ((1 : ℝ) / 4) / (2 * a) :=
      div_le_div_of_nonneg_right ht (by positivity)
    _ = 1 / (8 * a) := by
      field_simp [ha.ne']
      ring

/-- The exact two-stage bound for the logarithmic interpolation error. -/
theorem logChordError_bounds {a t : ℝ} (ha : 0 < a)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ logChordError a t ∧
      logChordError a t ≤ t * (1 - t) / (2 * a) ∧
        t * (1 - t) / (2 * a) ≤ 1 / (8 * a) :=
  ⟨logChordError_nonneg ha.le ht0 ht1, logChordError_le_quadratic ha ht0 ht1,
    quadraticChordBound_le_one_div_eight ha t⟩

/-- The uniform interpolation bound at a positive natural cutoff. -/
theorem logChordError_nat_bounds {N : ℕ} (hN : 1 ≤ N) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ logChordError (N : ℝ) t ∧
      logChordError (N : ℝ) t ≤ 1 / (8 * (N : ℝ)) := by
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : 0 < (N : ℝ) := by linarith
  obtain ⟨h0, hquad, hbound⟩ := logChordError_bounds hNpos ht0 ht1
  exact ⟨h0, hquad.trans hbound⟩

end InfoGeometry.Analysis.CenteredLogInterpolation
