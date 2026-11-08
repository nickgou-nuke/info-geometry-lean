/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.QuadraticArnoldVanishing
open InfoGeometry.Geometry.QuadraticArnoldNumerator
open NonIsoConf3LogWedgeObstruction

#print axioms polar_mul_coord
#print axioms polar_mul_coord_right
#print axioms mixedCore_zero
#print axioms numerator_xy
#print axioms numerator_xz
#print axioms numerator_yy
#print axioms numerator_yz
#print axioms numerator_zz
#print axioms numerator_zero_of_displacement_minors
#print axioms numerator_vanishes_iff

example : ∀ α β, numerator ⟨0,0,0,0⟩ ⟨1,0,0,0⟩ ⟨2,0,0,0⟩ α β = 0 := by
  apply numerator_zero_of_displacement_minors
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [coord, sub]

example : q4 (sub ⟨0,0,0,0⟩ ⟨1,0,0,0⟩) = 1 ∧
    q4 (sub ⟨1,0,0,0⟩ ⟨2,0,0,0⟩) = 1 ∧
    q4 (sub ⟨0,0,0,0⟩ ⟨2,0,0,0⟩) = 4 := by
  norm_num [q4, sub]

example : ¬ ∀ α β, numerator pointX pointY pointZ α β = 0 := by
  intro h
  have hz := h (0,0) (1,0)
  rw [numerator_counterexample] at hz
  norm_num at hz
