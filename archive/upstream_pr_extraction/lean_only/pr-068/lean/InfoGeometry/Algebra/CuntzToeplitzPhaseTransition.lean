import Mathlib.Tactic
import InfoGeometry.Algebra.CuntzTensorQuotient

noncomputable section

namespace InfoGeometry.Algebra.CuntzToeplitzPhaseTransition

open InfoGeometry.Algebra.CuntzTensorQuotient

/-!
# Native Cuntz--Toeplitz `𝒯₂` phase-transition identities

The carrier is the existing tensor-algebra quotient `CuntzToeplitzAlg 2`.
The vacuum defect is not an extra scalar field: it is the algebra element
`1 - (S₀ S₀† + S₁ S₁†)` in that quotient.
-/

abbrev NativeToeplitzTwo := CuntzToeplitzAlg 2

def QPlus : NativeToeplitzTwo :=
  toeplitzS 2 0 * toeplitzSdag 2 1

def QMinus : NativeToeplitzTwo :=
  toeplitzS 2 1 * toeplitzSdag 2 0

def vacuumDefect : NativeToeplitzTwo :=
  1 - (toeplitzS 2 0 * toeplitzSdag 2 0 +
    toeplitzS 2 1 * toeplitzSdag 2 1)

theorem qplus_nilpotent : QPlus * QPlus = 0 := by
  dsimp [QPlus]
  have h_assoc :
      toeplitzS 2 0 * toeplitzSdag 2 1 *
          (toeplitzS 2 0 * toeplitzSdag 2 1) =
        toeplitzS 2 0 *
          (toeplitzSdag 2 1 * toeplitzS 2 0) * toeplitzSdag 2 1 := by
    noncomm_ring
  rw [h_assoc, toeplitz_orthogonality]
  simp

theorem qminus_nilpotent : QMinus * QMinus = 0 := by
  dsimp [QMinus]
  have h_assoc :
      toeplitzS 2 1 * toeplitzSdag 2 0 *
          (toeplitzS 2 1 * toeplitzSdag 2 0) =
        toeplitzS 2 1 *
          (toeplitzSdag 2 0 * toeplitzS 2 1) * toeplitzSdag 2 0 := by
    noncomm_ring
  rw [h_assoc, toeplitz_orthogonality]
  simp

theorem qplus_qminus_product :
    QPlus * QMinus = toeplitzS 2 0 * toeplitzSdag 2 0 := by
  dsimp [QPlus, QMinus]
  have h_assoc :
      toeplitzS 2 0 * toeplitzSdag 2 1 *
          (toeplitzS 2 1 * toeplitzSdag 2 0) =
        toeplitzS 2 0 *
          (toeplitzSdag 2 1 * toeplitzS 2 1) * toeplitzSdag 2 0 := by
    noncomm_ring
  rw [h_assoc, toeplitz_orthogonality]
  simp

theorem qminus_qplus_product :
    QMinus * QPlus = toeplitzS 2 1 * toeplitzSdag 2 1 := by
  dsimp [QPlus, QMinus]
  have h_assoc :
      toeplitzS 2 1 * toeplitzSdag 2 0 *
          (toeplitzS 2 0 * toeplitzSdag 2 1) =
        toeplitzS 2 1 *
          (toeplitzSdag 2 0 * toeplitzS 2 0) * toeplitzSdag 2 1 := by
    noncomm_ring
  rw [h_assoc, toeplitz_orthogonality]
  simp

theorem toeplitz_susy_hamiltonian_identity :
    QPlus * QMinus + QMinus * QPlus + vacuumDefect = 1 := by
  rw [qplus_qminus_product, qminus_qplus_product]
  dsimp [vacuumDefect]
  noncomm_ring

theorem toeplitz_unbroken_vacuum_state
    (E : NativeToeplitzTwo → ℝ)
    (h_lin : ∀ x y, E (x + y) = E x + E y)
    (h_one : E 1 = 1)
    (h_zero_energy : E (QPlus * QMinus + QMinus * QPlus) = 0) :
    E vacuumDefect = 1 := by
  have h_exp :
      E (QPlus * QMinus + QMinus * QPlus + vacuumDefect) = E 1 := by
    rw [toeplitz_susy_hamiltonian_identity]
  rw [h_lin, h_zero_energy, zero_add, h_one] at h_exp
  exact h_exp

end InfoGeometry.Algebra.CuntzToeplitzPhaseTransition
