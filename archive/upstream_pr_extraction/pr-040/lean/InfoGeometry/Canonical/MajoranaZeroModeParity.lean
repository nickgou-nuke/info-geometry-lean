import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Matrix Complex

namespace MajoranaParity

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

namespace MajoranaPair

variable (gamma1 gamma2 : selfAdjoint (Matrix (Fin n) (Fin n) ℂ))

abbrev gamma1Val : Matrix (Fin n) (Fin n) ℂ := gamma1

abbrev gamma2Val : Matrix (Fin n) (Fin n) ℂ := gamma2

theorem gamma1_self_adjoint : (gamma1Val gamma1).conjTranspose = gamma1Val gamma1 := by
  simpa only [gamma1Val, Matrix.star_eq_conjTranspose] using gamma1.property

theorem gamma2_self_adjoint : (gamma2Val gamma2).conjTranspose = gamma2Val gamma2 := by
  simpa only [gamma2Val, Matrix.star_eq_conjTranspose] using gamma2.property

/-- Fermionic Parity Operator P = I * γ₁ * γ₂. -/
def parityOperator : Matrix (Fin n) (Fin n) ℂ :=
  I • (gamma1Val gamma1 * gamma2Val gamma2)

/-- **Theorem**: Majorana Anti-Commutation Swap γ₁ γ₂ = - γ₂ γ₁. -/
theorem maj_anti_swap
    (h_anti : gamma1Val gamma1 * gamma2Val gamma2 +
      gamma2Val gamma2 * gamma1Val gamma1 = 0) :
    gamma1Val gamma1 * gamma2Val gamma2 =
      - (gamma2Val gamma2 * gamma1Val gamma1) := by
  calc gamma1Val gamma1 * gamma2Val gamma2
    _ = (gamma1Val gamma1 * gamma2Val gamma2 +
        gamma2Val gamma2 * gamma1Val gamma1) -
      gamma2Val gamma2 * gamma1Val gamma1 := by noncomm_ring
    _ = 0 - gamma2Val gamma2 * gamma1Val gamma1 := by rw [h_anti]
    _ = - (gamma2Val gamma2 * gamma1Val gamma1) := by noncomm_ring

/-- **Theorem**: Fermionic Parity Operator Involution: P² = 1. -/
theorem parity_involution
    (h_sq1 : gamma1Val gamma1 * gamma1Val gamma1 = 1)
    (h_sq2 : gamma2Val gamma2 * gamma2Val gamma2 = 1)
    (h_anti : gamma1Val gamma1 * gamma2Val gamma2 +
      gamma2Val gamma2 * gamma1Val gamma1 = 0) :
    parityOperator gamma1 gamma2 * parityOperator gamma1 gamma2 = 1 := by
  dsimp [parityOperator]
  have h_prod : (gamma1Val gamma1 * gamma2Val gamma2) *
      (gamma1Val gamma1 * gamma2Val gamma2) =
      - (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have h_swap : gamma2Val gamma2 * gamma1Val gamma1 =
        - (gamma1Val gamma1 * gamma2Val gamma2) := by
      calc gamma2Val gamma2 * gamma1Val gamma1
        _ = (gamma1Val gamma1 * gamma2Val gamma2 +
            gamma2Val gamma2 * gamma1Val gamma1) -
          gamma1Val gamma1 * gamma2Val gamma2 := by noncomm_ring
        _ = 0 - gamma1Val gamma1 * gamma2Val gamma2 := by rw [h_anti]
        _ = - (gamma1Val gamma1 * gamma2Val gamma2) := by noncomm_ring
    calc (gamma1Val gamma1 * gamma2Val gamma2) *
        (gamma1Val gamma1 * gamma2Val gamma2)
      _ = gamma1Val gamma1 *
          (gamma2Val gamma2 * (gamma1Val gamma1 * gamma2Val gamma2)) := by
        rw [Matrix.mul_assoc (gamma1Val gamma1) (gamma2Val gamma2)
          (gamma1Val gamma1 * gamma2Val gamma2)]
      _ = gamma1Val gamma1 *
          ((gamma2Val gamma2 * gamma1Val gamma1) * gamma2Val gamma2) := by
        rw [Matrix.mul_assoc (gamma2Val gamma2) (gamma1Val gamma1) (gamma2Val gamma2)]
      _ = gamma1Val gamma1 *
          ((- (gamma1Val gamma1 * gamma2Val gamma2)) * gamma2Val gamma2) := by rw [h_swap]
      _ = - ((gamma1Val gamma1 * gamma1Val gamma1) *
          (gamma2Val gamma2 * gamma2Val gamma2)) := by noncomm_ring
      _ = - (1 * 1) := by
        rw [h_sq1, h_sq2]
      _ = - 1 := by noncomm_ring
  rw [Matrix.smul_mul, Matrix.mul_smul, h_prod, smul_smul, I_mul_I, neg_smul, one_smul, neg_neg]

/-- **Theorem**: Fermionic Parity Operator Hermiticity: P† = P. -/
theorem parity_self_adjoint
    (h_anti : gamma1Val gamma1 * gamma2Val gamma2 +
      gamma2Val gamma2 * gamma1Val gamma1 = 0) :
    (parityOperator gamma1 gamma2).conjTranspose = parityOperator gamma1 gamma2 := by
  dsimp [parityOperator]
  rw [conjTranspose_smul, conjTranspose_mul,
    gamma1_self_adjoint gamma1, gamma2_self_adjoint gamma2]
  have h_I : star I = - I := conj_I
  rw [h_I]
  have h_swap : gamma2Val gamma2 * gamma1Val gamma1 =
      - (gamma1Val gamma1 * gamma2Val gamma2) := by
    calc gamma2Val gamma2 * gamma1Val gamma1
      _ = (gamma1Val gamma1 * gamma2Val gamma2 +
          gamma2Val gamma2 * gamma1Val gamma1) -
        gamma1Val gamma1 * gamma2Val gamma2 := by noncomm_ring
      _ = 0 - gamma1Val gamma1 * gamma2Val gamma2 := by rw [h_anti]
      _ = - (gamma1Val gamma1 * gamma2Val gamma2) := by noncomm_ring
  rw [h_swap, smul_neg, neg_smul, neg_neg]

/-- Majorana Tunneling Hamiltonian H = I * μ * (γ₁ * γ₂). -/
def hamiltonian (mu : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  (I * (mu : ℂ)) • (gamma1Val gamma1 * gamma2Val gamma2)

/-- **Theorem**: Fermionic Parity Conservation under Majorana Hamiltonian: [P, H] = 0. -/
theorem parity_conservation (mu : ℝ) :
    parityOperator gamma1 gamma2 * hamiltonian gamma1 gamma2 mu -
      hamiltonian gamma1 gamma2 mu * parityOperator gamma1 gamma2 = 0 := by
  dsimp [parityOperator, hamiltonian]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul]
  have h_c : I * (I * (mu : ℂ)) = (I * (mu : ℂ)) * I := by ring
  rw [h_c, sub_self]

end MajoranaPair

end MajoranaParity
