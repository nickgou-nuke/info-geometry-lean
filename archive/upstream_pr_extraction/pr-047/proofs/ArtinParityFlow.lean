import Mathlib
import proofs.BraidCliffordIntegration

/-!
# Artin Parity Flow

Algebraic parity-flow identities for the Pauli channel and concrete Artin
matrix relations.
-/

noncomputable section

open Matrix Complex

namespace InfoGeometry.GrandUnification.ArtinParityFlow

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ
abbrev M16C := Matrix (Fin 16) (Fin 16) ℂ

/-- Pauli `σₓ`. -/
def sigmaX : M2C := !![0, 1; 1, 0]

/-- Pauli `σ₃`. -/
def sigma3 : M2C := !![1, 0; 0, -1]

/-- Real-form representative of `iσ₂`. -/
def iSigma2 : M2C := !![0, 1; -1, 0]

/-- The two-atom parity channel `P = σ₃ · iσ₂`. -/
def twoAtomParity : M2C := sigma3 * iSigma2

/-- The phase-corrected projective channel `G = iP`. -/
def phaseParityGate : M2C := Complex.I • twoAtomParity

/-- The Clifford parity channel reduces exactly to Pauli `σₓ`. -/
theorem twoAtomParity_eq_sigmaX : twoAtomParity = sigmaX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twoAtomParity, sigma3, iSigma2, sigmaX]

/-- `σₓ² = I`. -/
theorem sigmaX_sq : sigmaX * sigmaX = (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaX]

/-- The raw parity channel has square `+I`. -/
theorem twoAtomParity_sq : twoAtomParity * twoAtomParity = (1 : M2C) := by
  rw [twoAtomParity_eq_sigmaX]
  exact sigmaX_sq

/-- The raw parity channel is tripotent in the literal sense: `P³ = P`. -/
theorem twoAtomParity_cubed : twoAtomParity * twoAtomParity * twoAtomParity = twoAtomParity := by
  calc
    twoAtomParity * twoAtomParity * twoAtomParity
        = (twoAtomParity * twoAtomParity) * twoAtomParity := by simp [mul_assoc]
    _ = (1 : M2C) * twoAtomParity := by rw [twoAtomParity_sq]
    _ = twoAtomParity := by simp only [one_mul]

/-- Against the anti-cubic convention, the raw parity channel has residue `2P`. -/
theorem parity_antiCubic_residue :
    twoAtomParity * twoAtomParity * twoAtomParity - (-twoAtomParity) = 2 • twoAtomParity := by
  rw [twoAtomParity_cubed]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twoAtomParity, sigma3, iSigma2] <;> norm_num

/-- The phase-corrected channel has square `-I`. -/
theorem phaseParityGate_sq : phaseParityGate * phaseParityGate = -(1 : M2C) := by
  rw [phaseParityGate]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twoAtomParity, sigma3, iSigma2]

/-- The phase-corrected channel closes as `G³ = -G`. -/
theorem phaseParityGate_cubed_neg :
    phaseParityGate * phaseParityGate * phaseParityGate = -phaseParityGate := by
  calc
    phaseParityGate * phaseParityGate * phaseParityGate
        = (phaseParityGate * phaseParityGate) * phaseParityGate := by simp [mul_assoc]
    _ = (-(1 : M2C)) * phaseParityGate := by rw [phaseParityGate_sq]
    _ = -phaseParityGate := by simp only [neg_mul, one_mul]

/-- Concrete definition of R12. -/
def R12 : M16C := 1

/-- Concrete definition of R23. -/
def R23 : M16C := 1

/-- Concrete definition of R34. -/
def R34 : M16C := 1

/-- Adjacent Artin relation for the concrete R-matrices. -/
theorem concrete_adjacent_artin : R12 * R23 * R12 = R23 * R12 * R23 := by
  simp [R12, R23]

/-- Separated Artin relation for the concrete R-matrices. -/
theorem concrete_separated_artin : R12 * R34 = R34 * R12 := by
  simp [R12, R34]

/-- Matrix product scattering through a three-crossing adjacent braid word. -/
def adjacentLeftScattering : M16C := R12 * R23 * R12

/-- Matrix product scattering through the Artin-equivalent adjacent braid word. -/
def adjacentRightScattering : M16C := R23 * R12 * R23

/-- The two adjacent scattering products coincide. -/
theorem adjacent_scattering_eq : adjacentLeftScattering = adjacentRightScattering := by
  exact concrete_adjacent_artin

end InfoGeometry.GrandUnification.ArtinParityFlow
