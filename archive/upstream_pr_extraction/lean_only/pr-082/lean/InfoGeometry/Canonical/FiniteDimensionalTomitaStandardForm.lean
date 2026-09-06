import Mathlib

namespace InfoGeometry.Canonical

noncomputable section

abbrev HSMatrix := Matrix (Fin 2) (Fin 2) ℂ

def leftRepresentation (A X : HSMatrix) : HSMatrix := A * X

def rightRepresentation (A X : HSMatrix) : HSMatrix := X * A

theorem leftRepresentation_rightRepresentation_commute
    (A B X : HSMatrix) :
    leftRepresentation A (rightRepresentation B X) =
      rightRepresentation B (leftRepresentation A X) := by
  simp [leftRepresentation, rightRepresentation, Matrix.mul_assoc]

def modularConjugation (X : HSMatrix) : HSMatrix := star X

def modularOperator (rho rhoInv X : HSMatrix) : HSMatrix := rho * X * rhoInv

theorem modularOperator_eq_left_rightRepresentation
    (rho rhoInv X : HSMatrix) :
    modularOperator rho rhoInv X =
      leftRepresentation rho (rightRepresentation rhoInv X) := by
  simp [modularOperator, leftRepresentation, rightRepresentation, Matrix.mul_assoc]

def inverseModularOperator (rho rhoInv X : HSMatrix) : HSMatrix :=
  rhoInv * X * rho

theorem modularConjugation_sq (X : HSMatrix) :
    modularConjugation (modularConjugation X) = X := by
  simp [modularConjugation]

theorem modularConjugation_leftRepresentation
    (A X : HSMatrix) :
    modularConjugation (leftRepresentation A X) =
      rightRepresentation (star A) (modularConjugation X) := by
  simp [modularConjugation, leftRepresentation, rightRepresentation]

theorem modularConjugation_modularOperator
    (rho rhoInv X : HSMatrix)
    (hRho : star rho = rho)
    (hRhoInv : star rhoInv = rhoInv) :
    modularConjugation (modularOperator rho rhoInv
      (modularConjugation X)) =
      inverseModularOperator rho rhoInv X := by
  simp [modularConjugation, modularOperator, inverseModularOperator,
    hRho, hRhoInv, Matrix.star_mul, Matrix.mul_assoc]

theorem modularOperator_inverse_left
    (rho rhoInv X : HSMatrix)
    (hLeft : rhoInv * rho = (1 : HSMatrix))
    (hRight : rho * rhoInv = (1 : HSMatrix)) :
    inverseModularOperator rho rhoInv (modularOperator rho rhoInv X) = X := by
  simp only [inverseModularOperator, modularOperator, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc, hLeft, one_mul]
  simp

theorem modularOperator_inverse_right
    (rho rhoInv X : HSMatrix)
    (hLeft : rhoInv * rho = (1 : HSMatrix))
    (hRight : rho * rhoInv = (1 : HSMatrix)) :
    modularOperator rho rhoInv (inverseModularOperator rho rhoInv X) = X := by
  simp only [modularOperator, inverseModularOperator, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc, hRight, one_mul]
  simp

end
end InfoGeometry.Canonical
