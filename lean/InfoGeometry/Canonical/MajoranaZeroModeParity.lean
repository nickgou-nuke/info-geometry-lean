import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Matrix Complex

namespace MajoranaParity

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-- Majorana Zero Mode Pair Structure: γ₁ = γ₁†, γ₂ = γ₂†, γ₁² = 1, γ₂² = 1, {γ₁, γ₂} = 0. -/
structure MajoranaPair (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] where
  gamma1 : Matrix (Fin n) (Fin n) ℂ
  gamma2 : Matrix (Fin n) (Fin n) ℂ
  h_self_adj1 : gamma1.conjTranspose = gamma1
  h_self_adj2 : gamma2.conjTranspose = gamma2
  h_sq1 : gamma1 * gamma1 = 1
  h_sq2 : gamma2 * gamma2 = 1
  h_anti : gamma1 * gamma2 + gamma2 * gamma1 = 0

namespace MajoranaPair

variable (m : MajoranaPair n)

/-- Fermionic Parity Operator P = I * γ₁ * γ₂. -/
def parityOperator : Matrix (Fin n) (Fin n) ℂ :=
  I • (m.gamma1 * m.gamma2)

/-- **Theorem**: Majorana Anti-Commutation Swap γ₁ γ₂ = - γ₂ γ₁. -/
theorem maj_anti_swap : m.gamma1 * m.gamma2 = - (m.gamma2 * m.gamma1) := by
  have h := m.h_anti
  calc m.gamma1 * m.gamma2
    _ = (m.gamma1 * m.gamma2 + m.gamma2 * m.gamma1) - m.gamma2 * m.gamma1 := by noncomm_ring
    _ = 0 - m.gamma2 * m.gamma1 := by rw [h]
    _ = - (m.gamma2 * m.gamma1) := by noncomm_ring

/-- **Theorem**: Fermionic Parity Operator Involution: P² = 1. -/
theorem parity_involution : m.parityOperator * m.parityOperator = 1 := by
  dsimp [parityOperator]
  have h_prod : (m.gamma1 * m.gamma2) * (m.gamma1 * m.gamma2) = - (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have h_swap : m.gamma2 * m.gamma1 = - (m.gamma1 * m.gamma2) := by
      have h := m.h_anti
      calc m.gamma2 * m.gamma1
        _ = (m.gamma1 * m.gamma2 + m.gamma2 * m.gamma1) - m.gamma1 * m.gamma2 := by noncomm_ring
        _ = 0 - m.gamma1 * m.gamma2 := by rw [h]
        _ = - (m.gamma1 * m.gamma2) := by noncomm_ring
    calc (m.gamma1 * m.gamma2) * (m.gamma1 * m.gamma2)
      _ = m.gamma1 * (m.gamma2 * (m.gamma1 * m.gamma2)) := by rw [Matrix.mul_assoc m.gamma1 m.gamma2 (m.gamma1 * m.gamma2)]
      _ = m.gamma1 * ((m.gamma2 * m.gamma1) * m.gamma2) := by rw [Matrix.mul_assoc m.gamma2 m.gamma1 m.gamma2]
      _ = m.gamma1 * ((- (m.gamma1 * m.gamma2)) * m.gamma2) := by rw [h_swap]
      _ = - ((m.gamma1 * m.gamma1) * (m.gamma2 * m.gamma2)) := by noncomm_ring
      _ = - (1 * 1) := by rw [m.h_sq1, m.h_sq2]
      _ = - 1 := by noncomm_ring
  rw [Matrix.smul_mul, Matrix.mul_smul, h_prod, smul_smul, I_mul_I, neg_smul, one_smul, neg_neg]

/-- **Theorem**: Fermionic Parity Operator Hermiticity: P† = P. -/
theorem parity_self_adjoint : m.parityOperator.conjTranspose = m.parityOperator := by
  dsimp [parityOperator]
  rw [conjTranspose_smul, conjTranspose_mul, m.h_self_adj1, m.h_self_adj2]
  have h_I : star I = - I := conj_I
  rw [h_I]
  have h_swap : m.gamma2 * m.gamma1 = - (m.gamma1 * m.gamma2) := by
    have h := m.h_anti
    calc m.gamma2 * m.gamma1
      _ = (m.gamma1 * m.gamma2 + m.gamma2 * m.gamma1) - m.gamma1 * m.gamma2 := by noncomm_ring
      _ = 0 - m.gamma1 * m.gamma2 := by rw [h]
      _ = - (m.gamma1 * m.gamma2) := by noncomm_ring
  rw [h_swap, smul_neg, neg_smul, neg_neg]

/-- Majorana Tunneling Hamiltonian H = I * μ * (γ₁ * γ₂). -/
def hamiltonian (mu : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  (I * (mu : ℂ)) • (m.gamma1 * m.gamma2)

/-- **Theorem**: Fermionic Parity Conservation under Majorana Hamiltonian: [P, H] = 0. -/
theorem parity_conservation (mu : ℝ) :
    m.parityOperator * m.hamiltonian mu - m.hamiltonian mu * m.parityOperator = 0 := by
  dsimp [parityOperator, hamiltonian]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul]
  have h_c : I * (I * (mu : ℂ)) = (I * (mu : ℂ)) * I := by ring
  rw [h_c, sub_self]

end MajoranaPair

end MajoranaParity
