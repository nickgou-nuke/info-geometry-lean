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

namespace FullOperatorBKM

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-- Non-Commutative Density Matrix ρ over ℂ with invertible inverse ρ_inv. -/
structure NonCommutativeDensityOperator (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] where
  rho : Matrix (Fin n) (Fin n) ℂ
  rho_inv : Matrix (Fin n) (Fin n) ℂ
  h_inv_left : rho_inv * rho = 1
  h_inv_right : rho * rho_inv = 1

namespace NonCommutativeDensityOperator

variable (rho : NonCommutativeDensityOperator n)

/-- Tomita-Takesaki Modular Automorphism Operator Δ_ρ(X) = ρ * X * ρ⁻¹ on non-commutative matrix space. -/
def modularOperator (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  rho.rho * X * rho.rho_inv

/-- **Theorem**: Modular Operator Linearity: Δ_ρ(X + Y) = Δ_ρ(X) + Δ_ρ(Y). -/
theorem modular_operator_add (X Y : Matrix (Fin n) (Fin n) ℂ) :
    rho.modularOperator (X + Y) = rho.modularOperator X + rho.modularOperator Y := by
  dsimp [modularOperator]
  noncomm_ring

/-- **Theorem**: Modular Operator Identity State: Δ_ρ(1) = 1. -/
theorem modular_operator_one :
    rho.modularOperator 1 = 1 := by
  dsimp [modularOperator]
  rw [mul_one, rho.h_inv_right]

/-- **Theorem**: Modular Operator Multiplication Homomorphism: Δ_ρ(X * Y) = Δ_ρ(X) * Δ_ρ(Y). -/
theorem modular_operator_mul (X Y : Matrix (Fin n) (Fin n) ℂ) :
    rho.modularOperator (X * Y) = rho.modularOperator X * rho.modularOperator Y := by
  dsimp [modularOperator]
  have h_mid : rho.rho_inv * rho.rho = 1 := rho.h_inv_left
  calc rho.rho * (X * Y) * rho.rho_inv
    _ = rho.rho * X * 1 * Y * rho.rho_inv := by noncomm_ring
    _ = rho.rho * X * (rho.rho_inv * rho.rho) * Y * rho.rho_inv := by rw [h_mid]
    _ = (rho.rho * X * rho.rho_inv) * (rho.rho * Y * rho.rho_inv) := by noncomm_ring

/-- Full Non-Commutative Symmetrized BKM Operator Super-Operator J_ρ(X) = (1/2) * (ρ * X + X * ρ). -/
def bkmSymmetrizedSuperOperator (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (rho.rho * X + X * rho.rho)

/-- Full Non-Commutative BKM Quantum Fisher Inner Product <A, B>_BKM = Tr(Aᴴ * J_ρ(B)). -/
def fullBKMInnerProduct (A B : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  trace (A.conjTranspose * rho.bkmSymmetrizedSuperOperator B)

/-- **Theorem**: Vanishing Modular Commutator Trace: Tr([ρ, X]) = 0 for any non-commutative operator X. -/
theorem modular_commutator_trace_zero (X : Matrix (Fin n) (Fin n) ℂ) :
    trace (rho.rho * X - X * rho.rho) = 0 := by
  rw [trace_sub]
  have h_comm : trace (X * rho.rho) = trace (rho.rho * X) := trace_mul_comm X rho.rho
  rw [h_comm, sub_self]

end NonCommutativeDensityOperator

end FullOperatorBKM
