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

/-- The complete defect of the right `E22` tangent equation on an arbitrary
off-diagonal Zorn direction. This identifies every surviving coordinate, not
only the single basis witness used below. -/
theorem right_E22_offDiagonal_tangent_defect
    (u v : ZornVec3 R) (X : ZornVectorMatrix R) :
    ((R_map (R := R) (E22 : ZornVectorMatrix R) *
        L_map (R := R) (offDiagonal u v) +
      L_map (R := R) (offDiagonal u v) * R_map (R := R) E22 -
      L_map (R := R) (offDiagonal u v) : Module.End R (ZornVectorMatrix R)) X) =
      ⟨-ZornVec3.dot u X.w, fun i => X.b * u i,
        fun i => -(X.a * v i), ZornVec3.dot v X.v⟩ := by
  ext i <;>
    simp [Module.End.mul_apply, L_map, R_map, mul, E22, offDiagonal,
      _root_.sub_eq_add_neg, add, neg, ZornVec3.dot, ZornVec3.cross,
      Fin.sum_univ_three] <;>
    ring

/-- Exact criterion for the right `E22` tangent defect to vanish on an
arbitrary input.  The four conditions are precisely its four surviving
coordinates; no generic off-diagonal direction is silently assumed tangent. -/
theorem right_E22_offDiagonal_tangent_iff
    (u v : ZornVec3 R) (X : ZornVectorMatrix R) :
    ((R_map (R := R) (E22 : ZornVectorMatrix R) *
        L_map (R := R) (offDiagonal u v) +
      L_map (R := R) (offDiagonal u v) * R_map (R := R) E22 -
      L_map (R := R) (offDiagonal u v) : Module.End R (ZornVectorMatrix R)) X) = 0 ↔
      ZornVec3.dot u X.w = 0 ∧
        (∀ i, X.b * u i = 0) ∧
        (∀ i, X.a * v i = 0) ∧
        ZornVec3.dot v X.v = 0 := by
  rw [right_E22_offDiagonal_tangent_defect]
  constructor
  · intro h
    have ha := congrArg (fun Y : ZornVectorMatrix R => Y.a) h
    have hv := congrArg (fun Y : ZornVectorMatrix R => Y.v) h
    have hw := congrArg (fun Y : ZornVectorMatrix R => Y.w) h
    have hb := congrArg (fun Y : ZornVectorMatrix R => Y.b) h
    simp only [zero] at ha hv hw hb
    refine ⟨neg_eq_zero.mp ha, ?_, ?_, hb⟩
    · intro i
      exact congrFun hv i
    · intro i
      have hi := congrFun hw i
      exact neg_eq_zero.mp hi
  · rintro ⟨ha, huv, hvw, hb⟩
    ext <;> simp [zero, ha, huv, hvw, hb]

/-- The right-projector tangent equation, required as an operator identity,
admits only the zero off-diagonal direction. Evaluating at the native unit
detects both vectors; no cancellation or characteristic assumption is used.
The left-projector replacement is `left_E11_tangent_offDiagonal`. -/
theorem right_E22_offDiagonal_tangent_operator_iff
    (u v : ZornVec3 R) :
    (R_map (R := R) (E22 : ZornVectorMatrix R) *
        L_map (R := R) (offDiagonal u v) +
      L_map (R := R) (offDiagonal u v) * R_map (R := R) E22 -
      L_map (R := R) (offDiagonal u v) : Module.End R (ZornVectorMatrix R)) = 0 ↔
      u = 0 ∧ v = 0 := by
  constructor
  · intro h
    have hunit := LinearMap.congr_fun h (one : ZornVectorMatrix R)
    have hc := (right_E22_offDiagonal_tangent_iff u v one).1 hunit
    constructor
    · funext i
      change u i = 0
      simpa only [one, _root_.one_mul] using hc.2.1 i
    · funext i
      change v i = 0
      simpa only [one, _root_.one_mul] using hc.2.2.1 i
  · rintro ⟨rfl, rfl⟩
    apply LinearMap.ext
    intro X
    apply (right_E22_offDiagonal_tangent_iff 0 0 X).2
    simp [ZornVec3.dot]

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
  rw [h] at hd
  simp [_root_.sub_self] at hd
  have hv := congrArg (fun X : ZornVectorMatrix ℝ => X.v 0) hd
  norm_num [U, ZornVec3.basis] at hv

end
end InfoGeometry.Algebra.ZornVectorMatrix
