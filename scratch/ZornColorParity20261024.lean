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

/-- The commutator [L(-V_i), L(U_i)] in the signed color convention. -/
def signedColorParity (i : Fin 3) : Module.End R (ZornVectorMatrix R) :=
  L_map (R := R) (U i) * L_map (R := R) (V i) -
    L_map (R := R) (V i) * L_map (R := R) (U i)

theorem signedColorParity_eq_commutator (i : Fin 3) :
    signedColorParity (R := R) i =
      L_map (R := R) (-V i) * L_map (R := R) (U i) -
        L_map (R := R) (U i) * L_map (R := R) (-V i) := by
  have hn : L_map (R := R) (-(V i : ZornVectorMatrix R)) = -L_map (R := R) (V i) := by
    apply LinearMap.ext
    intro X
    change (-V i) * X = -(V i * X)
    exact neg_mul _ _
  rw [hn]
  unfold signedColorParity
  noncomm_ring

theorem signedColorParity_apply (i : Fin 3) (X : ZornVectorMatrix R) :
    signedColorParity i X =
      ⟨X.a, fun k => if k = i then X.v k else -X.v k,
        fun k => if k = i then -X.w k else X.w k, -X.b⟩ := by
  fin_cases i <;> ext k <;> (try fin_cases k) <;>
    simp [signedColorParity, Module.End.mul_apply, L_map, mul, sub, add, neg,
      U, V, ZornVec3.basis, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

theorem signedColorParity_sq (i : Fin 3) :
    signedColorParity (R := R) i * signedColorParity i = 1 := by
  apply LinearMap.ext
  intro X
  simp only [Module.End.mul_apply, signedColorParity_apply, Module.End.one_apply]
  ext k <;> (try split_ifs) <;> simp_all

theorem signedColorParity_product :
    signedColorParity (R := R) 0 * signedColorParity 1 * signedColorParity 2 =
      L_map (R := R) (diagonal 1 (-1)) := by
  apply LinearMap.ext
  intro X
  simp only [Module.End.mul_apply, signedColorParity_apply,
    left_diagonal_difference_apply]
  ext k <;> (try fin_cases k) <;> simp

/-- Right E22 is the submitted coordinate projection; its U action is not tangent. -/
theorem right_E22_upper_tangent_defect :
    (R_map (R := R) (E22 : ZornVectorMatrix R) * L_map (R := R) (U 0) +
      L_map (R := R) (U 0) * R_map (R := R) E22 - L_map (R := R) (U 0)) E22 = U 0 := by
  ext k <;> (try fin_cases k) <;>
    simp [Module.End.mul_apply, L_map, R_map, mul, E22, U, sub, add, neg,
      ZornVec3.basis, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

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
