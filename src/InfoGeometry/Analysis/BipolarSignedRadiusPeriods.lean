/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.BipolarCircleEnclosurePeriods

/-! # Circle periods for arbitrary signed radii

Radius negation shifts the parametrization by π, preserving orientation.
Geometric enclosure therefore uses the absolute radius.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarCircleEnclosurePeriods

open scoped Real
open Complex Metric
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Analysis.BipolarPeriodDescent
open InfoGeometry.Analysis.BipolarWindingPeriodLattice

/-- Radius negation is a phase shift, not a reversal of the contour. -/
theorem circleIntegral_neg_radius (f : ℂ → ℂ) (c : ℂ) (r : ℝ) :
    (∮ z in C(c, -r), f z) = ∮ z in C(c, r), f z := by
  let g : ℝ → ℂ := fun t => (circleMap 0 r t * I) • f (circleMap c r t)
  have hg : Function.Periodic g (2 * Real.pi) := by
    intro t
    simp only [g, periodic_circleMap 0 r t, periodic_circleMap c r t]
  unfold circleIntegral
  simp only [deriv_circleMap, circleMap_neg_radius]
  change (∫ t in 0..2 * Real.pi, g (t + Real.pi)) = ∫ t in 0..2 * Real.pi, g t
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_zero, add_comm] using hg.intervalIntegral_add_eq Real.pi 0

/-- The circle integral depends on the geometric radius `|r|`. -/
theorem circleIntegral_abs_radius (f : ℂ → ℂ) (c : ℂ) (r : ℝ) :
    (∮ z in C(c, |r|), f z) = ∮ z in C(c, r), f z := by
  rcases le_total 0 r with hr | hr
  · rw [abs_of_nonneg hr]
  · rw [abs_of_nonpos hr, circleIntegral_neg_radius]

/-- The regular-pole formula for either sign of the parametrization radius. -/
theorem circleIntegral_pole_eq_abs_enclosure
    {c w : ℂ} {r : ℝ} (hw : w ∉ sphere c |r|) :
    (∮ z in C(c, r), (z - w)⁻¹) =
      (poleEnclosureIndex c |r| w : ℂ) * (2 * Real.pi * I) := by
  rw [← circleIntegral_abs_radius]
  exact circleIntegral_pole_eq_enclosure (abs_nonneg r) hw

/-- Signed-radius circles land in the existing bipolar period lattice. -/
theorem circleIntegral_dlog01_eq_abs_circulationPeriod
    {c : ℂ} {r : ℝ}
    (h0 : (0 : ℂ) ∉ sphere c |r|) (h1 : (1 : ℂ) ∉ sphere c |r|) :
    (∮ z in C(c, r), dlog01 z) =
      circulationPeriod (circleEnclosurePair c |r|) := by
  rw [← circleIntegral_abs_radius]
  exact circleIntegral_dlog01_eq_circulationPeriod (abs_nonneg r) h0 h1

end InfoGeometry.Analysis.BipolarCircleEnclosurePeriods
