/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornLeftGrading
import Mathlib.Basic.Real.Basic

namespace InfoGeometry.Algebra.ZornVectorMatrix

variable {R : Type*} [CommRing R]
noncomputable section

/-- Right E22 is the submitted coordinate projection; its U action is not tangent. -/
theorem right_E22_upper_tangent_defect :
    (R_map (R := R) (E22 : ZornVectorMatrix R) * L_map (R := R) (U 0) +
      L_map (R := R) (U 0) * R_map (R := R) E22 - L_map (R := R) (U 0) : Module.End R (ZornVectorMatrix R)) E22 = U 0 := by
  ext k <;> (try fin_cases k) <;>
    simp [Module.End.mul_apply, L_map, R_map, mul, E22, U, _root_.sub_eq_add_neg, add, neg,
      ZornVec3.basis, ZornVec3.dot, ZornVec3.cross]

theorem right_E22_upper_not_tangent :
    R_map (R := ℝ) (E22 : ZornVectorMatrix ℝ) * L_map (R := ℝ) (U 0) +
      L_map (R := ℝ) (U 0) * R_map (R := ℝ) E22 ≠ L_map (R := ℝ) (U 0) := by
  intro h
  have hd := right_E22_upper_tangent_defect (R := ℝ)
  rw [h, sub_self] at hd
  have hv := congrArg (fun X : ZornVectorMatrix ℝ => X.v 0) hd
  norm_num [U, ZornVec3.basis] at hv

end
end InfoGeometry.Algebra.ZornVectorMatrix
