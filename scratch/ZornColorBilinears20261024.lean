/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.ZornSignedCAR
import InfoGeometry.Algebra.ZornLeftGrading
import InfoGeometry.OperatorAlgebra.QuadraticNoncommutativeIdentity

/-!
# Signed Zorn color bilinears

Uncompiled proposal against the expected promoted signed-CAR and action APIs.
Products below are compositions on the existing Zorn module, not Zorn products.
No adjoint identification, faithfulness, or superalgebra classification is claimed.
-/

noncomputable section

namespace InfoGeometry.Algebra.ZornColorBilinears

open ZornVectorMatrix
open InfoGeometry.OperatorAlgebra

variable {R : Type*} [CommRing R]

/-- The actual ordered bilinear in the U, -V convention. -/
def E (i j : Fin 3) : Module.End R (ZornVectorMatrix R) :=
  -(L_map (R := R) (U i) * L_map (-V j))

theorem E_action_U (i j k : Fin 3) :
    quadraticCommutator (E (R := R) i j) (L_map (U k)) =
      if j = k then L_map (U i) else 0 := by
  exact negative_car_bilinear_action_forward
    (fun i => L_map (R := R) (U i)) (fun j => L_map (R := R) (-V j))
    (fun i j => L_U_U_anticommutator i j)
    (fun i j => by
      simpa [quadraticAnticommutator, ite_smul] using
        (L_U_negV_anticommutator (R := R) i j)) i j k

theorem E_action_negV (i j k : Fin 3) :
    quadraticCommutator (E (R := R) i j) (L_map (-V k)) =
      if i = k then -(L_map (-V j)) else 0 := by
  exact negative_car_bilinear_action_backward
    (fun i => L_map (R := R) (U i)) (fun j => L_map (R := R) (-V j))
    (fun i j => L_negV_negV_anticommutator i j)
    (fun i j => by
      simpa [quadraticAnticommutator, ite_smul] using
        (L_U_negV_anticommutator (R := R) i j)) i j k

theorem E_commutator (i j l m : Fin 3) :
    quadraticCommutator (E (R := R) i j) (E l m) =
      (if j = l then E i m else 0) - (if m = i then E l j else 0) := by
  exact negative_car_bilinear_commutator
    (fun i => L_map (R := R) (U i)) (fun j => L_map (R := R) (-V j))
    (fun i j => L_U_U_anticommutator i j)
    (fun i j => L_negV_negV_anticommutator i j)
    (fun i j => by
      simpa [quadraticAnticommutator, ite_smul] using
        (L_U_negV_anticommutator (R := R) i j)) i j l m

/-- Two tangent left actions have a product commuting with the native projector.
This uses the tangent equations directly and remains valid in characteristic two. -/
theorem left_E11_commutes_offDiagonal_product (u v s t : ZornVec3 R) :
    L_map (R := R) E11 *
        (L_map (offDiagonal u v) * L_map (offDiagonal s t)) =
      (L_map (offDiagonal u v) * L_map (offDiagonal s t)) * L_map E11 := by
  have hx := eq_sub_of_add_eq (left_E11_tangent_offDiagonal (R := R) u v)
  have hy := eq_sub_of_add_eq (left_E11_tangent_offDiagonal (R := R) s t)
  calc
    _ = (L_map (R := R) E11 * L_map (offDiagonal u v)) *
        L_map (offDiagonal s t) := (mul_assoc _ _ _).symm
    _ = _ := by rw [hx]; noncomm_ring [hy]

theorem E_commutes_left_E11 (i j : Fin 3) :
    L_map (R := R) E11 * E i j = E i j * L_map E11 := by
  have hneg : (-V j : ZornVectorMatrix R) =
      offDiagonal 0 (-ZornVec3.basis j) := by
    ext k <;> simp [V, offDiagonal, zvm_neg_def, neg]
  have h := left_E11_commutes_offDiagonal_product (R := R)
    (ZornVec3.basis i) 0 0 (-ZornVec3.basis j)
  change L_map (R := R) E11 *
      (L_map (U i) * L_map (offDiagonal 0 (-ZornVec3.basis j))) =
    (L_map (U i) * L_map (offDiagonal 0 (-ZornVec3.basis j))) * L_map E11 at h
  simp only [E, hneg, mul_neg, neg_mul, h]

/-- The even bilinear commutes with the actual left diagonal-difference action. -/
theorem E_commutes_left_diagonal_difference (i j : Fin 3) :
    L_map (R := R) (diagonal 1 (-1)) * E i j =
      E i j * L_map (diagonal 1 (-1)) := by
  rw [left_diagonal_difference_eq_two_projector_sub_one]
  simp only [sub_mul, mul_sub, one_mul, mul_one, nsmul_mul, mul_nsmul,
    E_commutes_left_E11]

end InfoGeometry.Algebra.ZornColorBilinears
