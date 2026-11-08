/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.EmergentGeometry.HarmonicQuadraticRectangle

open InfoGeometry.EmergentGeometry.HarmonicRectangle

#print axioms harmonicQuadratic_harmonic
#print axioms harmonicQuadratic_coordinates
#print axioms symmetric_quadratic_integral
#print axioms harmonicQuadratic_vertical_integral
#print axioms harmonicQuadratic_rectangleIntegral
#print axioms harmonicQuadratic_rectangle_average
#print axioms harmonicQuadratic_center_mean_iff
#print axioms harmonic_rectangle_counterexample

-- The mixed xy term and arbitrary affine terms have the center mean on a nonsquare.
example (b c : ℂ) :
    rectangleIntegral (harmonicQuadratic Complex.I b c) 2 1 / 8 = c.re := by
  norm_num [harmonicQuadratic_rectangleIntegral]

-- The original nonzero mean discrepancy is retained in the full family.
example : rectangleIntegral (harmonicQuadratic 1 0 0) 2 1 / 8 = 1 := by
  norm_num [harmonicQuadratic_rectangleIntegral]

-- Positive squares recover the center value for every member of the family.
example (a b c : ℂ) {w : ℝ} (hw : 0 < w) :
    rectangleIntegral (harmonicQuadratic a b c) w w / (4 * w * w) =
      harmonicQuadratic a b c 0 :=
  (harmonicQuadratic_center_mean_iff a b c hw hw).mpr (Or.inr rfl)
