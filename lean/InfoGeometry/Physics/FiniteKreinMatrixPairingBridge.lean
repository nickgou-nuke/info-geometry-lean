import Mathlib

noncomputable section

namespace InfoGeometry.Physics.FiniteKreinMatrixPairingBridge

open Matrix

abbrev Carrier := Fin 2 → ℝ
abbrev Operator := Matrix (Fin 2) (Fin 2) ℝ

def eta : Operator := !![1, 0; 0, -1]

def kreinPairing (u v : Carrier) : ℝ :=
  u 0 * v 0 - u 1 * v 1

def kreinAdjoint (A : Operator) : Operator :=
  eta * Aᵀ * eta

theorem eta_symm : etaᵀ = eta := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eta]

theorem eta_sq : eta * eta = (1 : Operator) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eta, Matrix.mul_apply, Fin.sum_univ_two]

theorem kreinAdjoint_involutive (A : Operator) :
    kreinAdjoint (kreinAdjoint A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kreinAdjoint, eta, Matrix.mul_apply, Fin.sum_univ_two]

theorem krein_pairing_adjoint (A : Operator) (u v : Carrier) :
    kreinPairing (A.mulVec u) v =
      kreinPairing u ((kreinAdjoint A).mulVec v) := by
  simp [kreinPairing, kreinAdjoint, eta, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

end InfoGeometry.Physics.FiniteKreinMatrixPairingBridge
