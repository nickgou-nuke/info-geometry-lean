/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.QuadraticArnoldNumerator
open InfoGeometry.Geometry.QuadraticArnoldNumerator
open NonIsoConf3LogWedgeObstruction

#print axioms numerator_skew
#print axioms numerator_diagonal
#print axioms numerator_dx0dy0
#print axioms numerator_counterexample
#print axioms numerator_xx
#print axioms displacement_minors_of_numerator_zero

example : ¬ ∀ α β, numerator pointX pointY pointZ α β = 0 := by
  intro h
  have hz := h (0, 0) (1, 0)
  rw [numerator_counterexample] at hz
  norm_num at hz

example : q4 (sub pointY pointZ) ≠ 0 := by
  norm_num [q4, sub, pointY, pointZ]

example : displacementMinor pointX pointY pointZ 0 1 ≠ 0 := by
  norm_num [displacementMinor, coord, sub, pointX, pointY, pointZ]
