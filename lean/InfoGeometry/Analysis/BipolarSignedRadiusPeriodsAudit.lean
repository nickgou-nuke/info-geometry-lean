/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.BipolarSignedRadiusPeriods

#print axioms InfoGeometry.Analysis.BipolarCircleEnclosurePeriods.circleIntegral_neg_radius
#print axioms InfoGeometry.Analysis.BipolarCircleEnclosurePeriods.circleIntegral_abs_radius
#print axioms InfoGeometry.Analysis.BipolarCircleEnclosurePeriods.circleIntegral_pole_eq_abs_enclosure
#print axioms InfoGeometry.Analysis.BipolarCircleEnclosurePeriods.circleIntegral_dlog01_eq_abs_circulationPeriod

open Complex Metric
open InfoGeometry.Analysis.BipolarCircleEnclosurePeriods

-- The signed-radius formula recovers the nonzero period of the counterexample.
example : (∮ z in C((0 : ℂ), (-1 : ℝ)), (z - 0)⁻¹) =
    (2 * Real.pi * I : ℂ) := by
  rw [circleIntegral_pole_eq_abs_enclosure (by norm_num [mem_sphere])]
  norm_num [poleEnclosureIndex]

-- Degenerate circles away from the pole are included, rather than excluded.
example : (∮ z in C((1 : ℂ), (0 : ℝ)), (z - 0)⁻¹) = 0 := by
  rw [circleIntegral_pole_eq_abs_enclosure (by norm_num [mem_sphere])]
  norm_num [poleEnclosureIndex]
