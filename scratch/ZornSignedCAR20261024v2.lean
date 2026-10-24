/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornDerivationBridge
import InfoGeometry.Canonical.CattoGurseySplitBasis
import Mathlib.Basic.Real.Basic

/-! Negative CAR for the explicit U, -V convention on the native Zorn module.
No grading, adjoint identification, or octonion-product representation is asserted.
-/

namespace InfoGeometry.Algebra

section Alternative
variable {R A : Type*} [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem L_map_square_of_left_alternative
    (h : ∀ x y : A, (x * x) * y = x * (x * y)) (x : A) :
    L_map (R := R) x * L_map x = L_map (x * x) := by
  apply LinearMap.ext
  intro y
  exact (h x y).symm

theorem L_map_anticommutator_of_left_alternative
    (h : ∀ x y : A, (x * x) * y = x * (x * y)) (x y : A) :
    L_map (R := R) x * L_map y + L_map y * L_map x =
      L_map (x * y + y * x) := by
  apply LinearMap.ext
  intro z
  change x * (y * z) + y * (x * z) = (x * y + y * x) * z
  rw [add_mul]
  exact (alternative_left_linearized h x y z).symm
end Alternative

namespace ZornVectorMatrix
variable {R : Type*} [CommRing R]

theorem L_U_square_zero (i : Fin 3) :
    L_map (R := R) (U i) * L_map (U i) = 0 := by
  rw [L_map_square_of_left_alternative zorn_left_alternative]
  have h : (U i : ZornVectorMatrix R) * U i = 0 := U_mul_self_zero i
  rw [h]
  apply LinearMap.ext
  intro z
  exact zero_mul z

theorem L_negV_square_zero (i : Fin 3) :
    L_map (R := R) (-V i) * L_map (-V i) = 0 := by
  rw [L_map_square_of_left_alternative zorn_left_alternative, neg_mul_neg]
  have h : (V i : ZornVectorMatrix R) * V i = 0 := V_mul_self_zero i
  rw [h]
  apply LinearMap.ext
  intro z
  exact zero_mul z

theorem L_U_U_anticommutator (i j : Fin 3) :
    L_map (R := R) (U i) * L_map (U j) + L_map (U j) * L_map (U i) = 0 := by
  rw [L_map_anticommutator_of_left_alternative zorn_left_alternative]
  have h := (InfoGeometry.Canonical.GunaydinGursey.car_relations (R := R) i j).2.1
  change (-U i : ZornVectorMatrix R) * (-U j) + (-U j) * (-U i) = 0 at h
  simp only [neg_mul_neg] at h
  rw [h]
  apply LinearMap.ext
  intro z
  exact zero_mul z

theorem L_negV_negV_anticommutator (i j : Fin 3) :
    L_map (R := R) (-V i) * L_map (-V j) + L_map (-V j) * L_map (-V i) = 0 := by
  rw [L_map_anticommutator_of_left_alternative zorn_left_alternative]
  have h := (InfoGeometry.Canonical.GunaydinGursey.car_relations (R := R) i j).1
  change (V i : ZornVectorMatrix R) * V j + V j * V i = 0 at h
  rw [neg_mul_neg, neg_mul_neg, h]
  apply LinearMap.ext
  intro z
  exact zero_mul z

/-- U, -V has negative mixed CAR; the star-labelled Catto basis is V, -U. -/
theorem L_U_negV_anticommutator (i j : Fin 3) :
    L_map (R := R) (U i) * L_map (-V j) + L_map (-V j) * L_map (U i) =
      (if i = j then (-1 : R) else 0) • (1 : Module.End R (ZornVectorMatrix R)) := by
  rw [L_map_anticommutator_of_left_alternative zorn_left_alternative]
  have h := (InfoGeometry.Canonical.GunaydinGursey.car_relations (R := R) j i).2.2
  change (V j : ZornVectorMatrix R) * (-U i) + (-U i) * V j =
    scalar (if j = i then -1 else 0) at h
  have he : (U i : ZornVectorMatrix R) * (-V j) + (-V j) * U i =
      scalar (if i = j then -1 else 0) := by
    simpa only [mul_neg, neg_mul, add_comm, eq_comm] using h
  rw [he]
  apply LinearMap.ext
  intro z
  exact scalar_mul _ z

/-- The proposed ordered E01 operator is nonzero on the native vector U1. -/
theorem neg_L_U0_L_negV1_apply_U1 :
    (-(L_map (R := ℝ) (U 0) * L_map (-V 1)) : Module.End ℝ (ZornVectorMatrix ℝ)) (U 1) = U 0 := by
  change neg (mul (U 0) (mul (neg (V 1)) (U 1))) = (U 0 : ZornVectorMatrix ℝ)
  rw [show mul (neg (V 1)) (U 1) = neg E22 by
    change (-V 1 : ZornVectorMatrix ℝ) * U 1 = -E22
    rw [neg_mul]
    exact congrArg Neg.neg (V_mul_U_self 1)]
  ext i <;> (try fin_cases i) <;>
    norm_num [mul, neg, U, E22, ZornVec3.dot, ZornVec3.cross,
      ZornVec3.basis, Fin.sum_univ_three]

/-- The off-diagonal odd anticommutator cannot be identified with this E01. -/
theorem L_U0_negV1_anticommutator_ne_ordered :
    L_map (R := ℝ) (U 0) * L_map (-V 1) + L_map (-V 1) * L_map (U 0) ≠
      -(L_map (R := ℝ) (U 0) * L_map (-V 1)) := by
  rw [L_U_negV_anticommutator]
  have hij : (0 : Fin 3) ≠ 1 := by decide
  simp only [hij, if_false, zero_smul]
  intro h
  have he := LinearMap.congr_fun h (U 1)
  rw [neg_L_U0_L_negV1_apply_U1] at he
  change (zero : ZornVectorMatrix ℝ) = U 0 at he
  have hc := congrArg (fun X : ZornVectorMatrix ℝ => X.v 0) he
  norm_num [zero, U, ZornVec3.basis] at hc

end ZornVectorMatrix
end InfoGeometry.Algebra
