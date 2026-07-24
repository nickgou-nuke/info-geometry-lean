import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.RelativeModularBlockDiagonalCore

Pure algebraic core for projector block-diagonalization on the doubled-real
carrier.

This file intentionally contains no modular/physics owner logic. It only
packages the reusable idempotent+commutation block-vanishing lemma.
-/

namespace InfoGeometry.Canonical.RelativeModularBlockDiagonalCore

open InfoGeometry.Krein

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

private noncomputable instance : NormedRing EndH := inferInstance
private noncomputable instance : NormedAlgebra ℝ EndH := inferInstance
private instance : IsTopologicalRing EndH := inferInstance
private instance : CompleteSpace EndH := inferInstance
private instance : SMulCommClass ℝ EndH EndH := inferInstance
private instance : IsScalarTower ℝ EndH EndH := inferInstance

/--
Generic two-block decoupling:
if `P^2 = P` and `P` commutes with `R`, then off-diagonal blocks vanish.
-/
@[rep_depth transport]
-- theorem-class: closure
theorem block_diagonal_of_commute_idempotent
    (P R : EndH)
    (hP : P * P = P)
    (hPR : Commute P R) :
    ((1 : EndH) - P) * R * P = 0
      ∧
    P * R * ((1 : EndH) - P) = 0 := by
  let _ : CompleteSpace E := inferInstance
  have hComm : P * R = R * P := hPR.eq
  constructor
  · calc
      ((1 : EndH) - P) * R * P
          = ((1 : EndH) * R - P * R) * P := by
              rw [sub_mul]
      _ = (1 : EndH) * R * P - (P * R) * P := by
            rw [sub_mul]
      _ = R * P - P * R * P := by
            rw [one_mul, mul_assoc]
      _ = R * P - (R * P) * P := by
            rw [hComm]
      _ = R * P - R * (P * P) := by
            rw [mul_assoc]
      _ = R * P - R * P := by
            rw [hP]
      _ = 0 := sub_self _
  · calc
      P * R * ((1 : EndH) - P)
          = P * R * (1 : EndH) - P * R * P := by
              rw [mul_sub]
      _ = P * R - P * R * P := by
            rw [mul_one]
      _ = P * R - P * (R * P) := by
            rw [mul_assoc]
      _ = P * R - P * (P * R) := by
            rw [hComm]
      _ = P * R - (P * P) * R := by
            rw [mul_assoc]
      _ = P * R - P * R := by
            rw [hP]
      _ = 0 := sub_self _

end Core

end InfoGeometry.Canonical.RelativeModularBlockDiagonalCore
