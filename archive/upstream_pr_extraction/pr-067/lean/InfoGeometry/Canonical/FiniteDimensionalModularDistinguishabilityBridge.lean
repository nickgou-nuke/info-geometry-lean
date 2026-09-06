import InfoGeometry.Canonical.FiniteDimensionalTomitaStandardForm
import Mathlib

/-!
# Finite-dimensional modular distinguishability bridge

This file is deliberately small.  It reuses the existing finite Tomita
standard-form owner and packages the explicit left/right modular operators
as a bridge layer.

It does not yet claim Bures/SLD positivity, BKM Hessians, or a full density
manifold.  Those require a separate state-dependent operator theory.
-/

namespace InfoGeometry.Canonical

noncomputable section

abbrev ModularHSMatrix := HSMatrix

/-- The algebraic trace pairing on the finite Tomita carrier. -/
def modularTracePairing (X Y : ModularHSMatrix) : ℂ :=
  Matrix.trace (X * Y)

/-- The algebraic trace pairing is cyclically symmetric. -/
theorem modularTracePairing_symm (X Y : ModularHSMatrix) :
    modularTracePairing X Y = modularTracePairing Y X := by
  simp [modularTracePairing]
  exact Matrix.trace_mul_comm X Y

/-- Left and right representations are adjoint for the algebraic trace pairing. -/
theorem modularTracePairing_left_rightRepresentation
    (rho X Y : ModularHSMatrix) :
    modularTracePairing (leftRepresentation rho X) Y =
      modularTracePairing X (rightRepresentation rho Y) := by
  dsimp [modularTracePairing, leftRepresentation, rightRepresentation]
  rw [Matrix.mul_assoc]
  calc
    Matrix.trace (rho * (X * Y)) = Matrix.trace ((X * Y) * rho) := by
      exact Matrix.trace_mul_comm rho (X * Y)
    _ = Matrix.trace (X * (Y * rho)) := by
      simp [Matrix.mul_assoc]

/-- Right multiplication is adjoint to left multiplication for the algebraic
trace pairing as well. -/
theorem modularTracePairing_right_leftRepresentation
    (rho X Y : ModularHSMatrix) :
    modularTracePairing (rightRepresentation rho X) Y =
      modularTracePairing X (leftRepresentation rho Y) := by
  simpa [modularTracePairing, leftRepresentation, rightRepresentation,
    Matrix.mul_assoc] using Matrix.trace_mul_comm X (Y * rho)

/-- Modular conjugation intertwines the right representation with the left
representation of the adjoint matrix. -/
theorem modularConjugation_rightRepresentation
    (A X : ModularHSMatrix) :
    modularConjugation (rightRepresentation A X) =
      leftRepresentation (star A) (modularConjugation X) := by
  simp [modularConjugation, leftRepresentation, rightRepresentation]

theorem finiteModularConjugation_sq (X : ModularHSMatrix) :
    modularConjugation (modularConjugation X) = X := by
  simp [modularConjugation]

theorem modularConjugation_relativeOperator
    (rho rhoInv X : ModularHSMatrix)
    (hRho : star rho = rho)
    (hRhoInv : star rhoInv = rhoInv) :
    modularConjugation (modularOperator rho rhoInv
      (modularConjugation X)) =
      inverseModularOperator rho rhoInv X := by
  simpa using
    modularConjugation_modularOperator rho rhoInv X hRho hRhoInv

end

end InfoGeometry.Canonical
