/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornLeftGrading

/-! # Three-mode parity product on the native Zorn module

The signed lower operator is `-L_map (V (R := R) i)`, not a Hilbert-space adjoint.
The mode commutator with that signed lower operator is exactly the ordinary
commutator `L_map (U (R := R) i) * L_map (V (R := R) i) - L_map (V (R := R) i) * L_map (U (R := R) i)`.
-/

namespace InfoGeometry.Algebra.ZornVectorMatrix

variable {R : Type*} [CommRing R]

noncomputable section

/-- Individual mode parity on the native eight coordinates. -/
theorem left_mode_commutator_apply (i : Fin 3) (X : ZornVectorMatrix R) :
    (L_map (R := R) (U (R := R) i) * L_map (R := R) (V (R := R) i) -
      L_map (R := R) (V (R := R) i) * L_map (R := R) (U (R := R) i)) X =
      ⟨X.a, (fun k => if k = i then X.v k else -X.v k),
        (fun k => if k = i then -X.w k else X.w k), -X.b⟩ := by
  change sub (mul (U (R := R) i) (mul (V (R := R) i) X)) (mul (V (R := R) i) (mul (U (R := R) i) X)) = _
  fin_cases i <;> ext k <;> (try fin_cases k) <;>
    simp [sub, add, neg, mul, U, V, ZornVec3.basis,
      ZornVec3.dot, ZornVec3.cross]

/-- The normalization of one native unsigned CAR pair. -/
theorem left_U_V_same_car (i : Fin 3) :
    L_map (R := R) (U (R := R) i) * L_map (R := R) (V (R := R) i) +
      L_map (R := R) (V (R := R) i) * L_map (R := R) (U (R := R) i) =
      (1 : Module.End R (ZornVectorMatrix R)) := by
  apply LinearMap.ext
  intro X
  change add (mul (U (R := R) i) (mul (V (R := R) i) X)) (mul (V (R := R) i) (mul (U (R := R) i) X)) = X
  fin_cases i <;> ext k <;> (try fin_cases k) <;>
    simp [add, mul, U, V, ZornVec3.basis,
      ZornVec3.dot, ZornVec3.cross]

/-- With signed dual `-L_V`, its commutator with `L_U` is `1 - 2 L_V L_U`. -/
theorem left_signed_mode_commutator_eq (i : Fin 3) :
    (-L_map (R := R) (V (R := R) i)) * L_map (R := R) (U (R := R) i) -
      L_map (R := R) (U (R := R) i) * (-L_map (R := R) (V (R := R) i)) =
      1 - 2 • (L_map (R := R) (V (R := R) i) * L_map (R := R) (U (R := R) i)) := by
  have h := left_U_V_same_car (R := R) i
  calc
    _ = (L_map (R := R) (U (R := R) i) * L_map (R := R) (V (R := R) i) +
        L_map (R := R) (V (R := R) i) * L_map (R := R) (U (R := R) i)) -
        2 • (L_map (R := R) (V (R := R) i) * L_map (R := R) (U (R := R) i)) := by
      simp only [two_nsmul]
      noncomm_ring
    _ = _ := by rw [h]

/-- The three signed-dual mode involutions multiply to the native left grading. -/
theorem left_three_mode_product :
    let G := fun i : Fin 3 =>
      (-L_map (R := R) (V (R := R) i)) * L_map (R := R) (U (R := R) i) -
        L_map (R := R) (U (R := R) i) * (-L_map (R := R) (V (R := R) i))
    G 0 * G 1 * G 2 = L_map (R := R) (diagonal (R := R) 1 (-1)) := by
  let F := fun i : Fin 3 =>
    L_map (R := R) (U (R := R) i) * L_map (R := R) (V (R := R) i) -
      L_map (R := R) (V (R := R) i) * L_map (R := R) (U (R := R) i)
  have hF (i : Fin 3) :
      (-L_map (R := R) (V (R := R) i)) * L_map (R := R) (U (R := R) i) -
        L_map (R := R) (U (R := R) i) * (-L_map (R := R) (V (R := R) i)) = F i := by
    dsimp [F]
    noncomm_ring
  dsimp only
  rw [hF, hF, hF]
  apply LinearMap.ext
  intro X
  simp only [Module.End.mul_apply, F, left_mode_commutator_apply,
    left_diagonal_difference_apply]
  ext k <;> (try fin_cases k) <;> simp

end
end InfoGeometry.Algebra.ZornVectorMatrix
