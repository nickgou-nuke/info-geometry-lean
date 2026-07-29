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

/-- Majorana Zero Mode Pair Structure: γ₁ = γ₁†, γ₂ = γ₂†, γ₁² = 1, γ₂² = 1, {γ₁, γ₂} = 0. -/
structure MajoranaPair (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] where
  gamma1 : selfAdjoint (Matrix (Fin n) (Fin n) ℂ)
  gamma2 : selfAdjoint (Matrix (Fin n) (Fin n) ℂ)
  h_sq1 : (gamma1 : Matrix (Fin n) (Fin n) ℂ) * gamma1 = 1
  h_sq2 : (gamma2 : Matrix (Fin n) (Fin n) ℂ) * gamma2 = 1
  h_anti : (gamma1 : Matrix (Fin n) (Fin n) ℂ) * gamma2 +
      (gamma2 : Matrix (Fin n) (Fin n) ℂ) * gamma1 = 0

namespace MajoranaPair

variable (m : MajoranaPair n)

def gamma1Val : Matrix (Fin n) (Fin n) ℂ := m.gamma1

def gamma2Val : Matrix (Fin n) (Fin n) ℂ := m.gamma2

theorem gamma1_self_adjoint : (gamma1Val m).conjTranspose = gamma1Val m := by
  simpa only [gamma1Val, Matrix.star_eq_conjTranspose] using m.gamma1.property

theorem gamma2_self_adjoint : (gamma2Val m).conjTranspose = gamma2Val m := by
  simpa only [gamma2Val, Matrix.star_eq_conjTranspose] using m.gamma2.property

/-- Fermionic Parity Operator P = I * γ₁ * γ₂. -/
def parityOperator : Matrix (Fin n) (Fin n) ℂ :=
  I • (gamma1Val m * gamma2Val m)

/-- **Theorem**: Majorana Anti-Commutation Swap γ₁ γ₂ = - γ₂ γ₁. -/
theorem maj_anti_swap : gamma1Val m * gamma2Val m = - (gamma2Val m * gamma1Val m) := by
  have h := m.h_anti
  change gamma1Val m * gamma2Val m + gamma2Val m * gamma1Val m = 0 at h
  calc gamma1Val m * gamma2Val m
    _ = (gamma1Val m * gamma2Val m + gamma2Val m * gamma1Val m) -
      gamma2Val m * gamma1Val m := by noncomm_ring
    _ = 0 - gamma2Val m * gamma1Val m := by rw [h]
    _ = - (gamma2Val m * gamma1Val m) := by noncomm_ring

/-- **Theorem**: Fermionic Parity Operator Involution: P² = 1. -/
theorem parity_involution : m.parityOperator * m.parityOperator = 1 := by
  dsimp [parityOperator]
  have h_prod : (gamma1Val m * gamma2Val m) * (gamma1Val m * gamma2Val m) =
      - (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have h_swap : gamma2Val m * gamma1Val m = - (gamma1Val m * gamma2Val m) := by
      have h := m.h_anti
      change gamma1Val m * gamma2Val m + gamma2Val m * gamma1Val m = 0 at h
      calc gamma2Val m * gamma1Val m
        _ = (gamma1Val m * gamma2Val m + gamma2Val m * gamma1Val m) -
          gamma1Val m * gamma2Val m := by noncomm_ring
        _ = 0 - gamma1Val m * gamma2Val m := by rw [h]
        _ = - (gamma1Val m * gamma2Val m) := by noncomm_ring
    calc (gamma1Val m * gamma2Val m) * (gamma1Val m * gamma2Val m)
      _ = gamma1Val m * (gamma2Val m * (gamma1Val m * gamma2Val m)) := by
        rw [Matrix.mul_assoc (gamma1Val m) (gamma2Val m) (gamma1Val m * gamma2Val m)]
      _ = gamma1Val m * ((gamma2Val m * gamma1Val m) * gamma2Val m) := by
        rw [Matrix.mul_assoc (gamma2Val m) (gamma1Val m) (gamma2Val m)]
      _ = gamma1Val m * ((- (gamma1Val m * gamma2Val m)) * gamma2Val m) := by rw [h_swap]
      _ = - ((gamma1Val m * gamma1Val m) * (gamma2Val m * gamma2Val m)) := by noncomm_ring
      _ = - (1 * 1) := by
        have hsq1 := m.h_sq1
        have hsq2 := m.h_sq2
        change gamma1Val m * gamma1Val m = 1 at hsq1
        change gamma2Val m * gamma2Val m = 1 at hsq2
        rw [hsq1, hsq2]
      _ = - 1 := by noncomm_ring
  rw [Matrix.smul_mul, Matrix.mul_smul, h_prod, smul_smul, I_mul_I, neg_smul, one_smul, neg_neg]

/-- **Theorem**: Fermionic Parity Operator Hermiticity: P† = P. -/
theorem parity_self_adjoint : m.parityOperator.conjTranspose = m.parityOperator := by
  dsimp [parityOperator]
  rw [conjTranspose_smul, conjTranspose_mul, gamma1_self_adjoint m, gamma2_self_adjoint m]
  have h_I : star I = - I := conj_I
  rw [h_I]
  have h_swap : gamma2Val m * gamma1Val m = - (gamma1Val m * gamma2Val m) := by
    have h := m.h_anti
    change gamma1Val m * gamma2Val m + gamma2Val m * gamma1Val m = 0 at h
    calc gamma2Val m * gamma1Val m
      _ = (gamma1Val m * gamma2Val m + gamma2Val m * gamma1Val m) -
        gamma1Val m * gamma2Val m := by noncomm_ring
      _ = 0 - gamma1Val m * gamma2Val m := by rw [h]
      _ = - (gamma1Val m * gamma2Val m) := by noncomm_ring
  rw [h_swap, smul_neg, neg_smul, neg_neg]

/-- Majorana Tunneling Hamiltonian H = I * μ * (γ₁ * γ₂). -/
def hamiltonian (mu : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  (I * (mu : ℂ)) • (gamma1Val m * gamma2Val m)

/-- **Theorem**: Fermionic Parity Conservation under Majorana Hamiltonian: [P, H] = 0. -/
theorem parity_conservation (mu : ℝ) :
    m.parityOperator * m.hamiltonian mu - m.hamiltonian mu * m.parityOperator = 0 := by
  dsimp [parityOperator, hamiltonian]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul]
  have h_c : I * (I * (mu : ℂ)) = (I * (mu : ℂ)) * I := by ring
  rw [h_c, sub_self]

end MajoranaPair

end MajoranaParity
