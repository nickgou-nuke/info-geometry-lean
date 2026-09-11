import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Matrix Complex

namespace FullOperatorBKM

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-- Invertible Matrix State Parameter ρ over ℂ with inverse ρ_inv (Algebraic Density Data Carrier). -/
abbrev NonCommutativeDensityOperator (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] :=
  Matrix.GeneralLinearGroup (Fin n) ℂ

namespace NonCommutativeDensityOperator

variable (D : NonCommutativeDensityOperator n)

def rho : Matrix (Fin n) (Fin n) ℂ := (D : Matrix (Fin n) (Fin n) ℂ)

def rho_inv : Matrix (Fin n) (Fin n) ℂ :=
  ((D⁻¹ : NonCommutativeDensityOperator n) : Matrix (Fin n) (Fin n) ℂ)

theorem h_inv_left : rho_inv D * rho D = 1 := by
  simp [rho, rho_inv]

theorem h_inv_right : rho D * rho_inv D = 1 := by
  simp [rho, rho_inv]

/-- Finite Matrix Inner Automorphism Super-Operator Δ_ρ(X) = ρ * X * ρ⁻¹ (Matrix Modular Conjugation Superoperator). -/
def modularOperator (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  rho D * X * rho_inv D

/-- **Theorem**: Modular Operator Linearity: Δ_ρ(X + Y) = Δ_ρ(X) + Δ_ρ(Y). -/
theorem modular_operator_add (X Y : Matrix (Fin n) (Fin n) ℂ) :
    D.modularOperator (X + Y) = D.modularOperator X + D.modularOperator Y := by
  dsimp [modularOperator]
  noncomm_ring

/-- **Theorem**: Modular Operator Identity State: Δ_ρ(1) = 1. -/
theorem modular_operator_one :
    D.modularOperator 1 = 1 := by
  dsimp [modularOperator]
  rw [mul_one, h_inv_right D]

/-- **Theorem**: Modular Operator Multiplication Homomorphism: Δ_ρ(X * Y) = Δ_ρ(X) * Δ_ρ(Y). -/
theorem modular_operator_mul (X Y : Matrix (Fin n) (Fin n) ℂ) :
    D.modularOperator (X * Y) = D.modularOperator X * D.modularOperator Y := by
  dsimp [modularOperator]
  have h_mid : rho_inv D * rho D = 1 := h_inv_left D
  calc rho D * (X * Y) * rho_inv D
    _ = rho D * X * 1 * Y * rho_inv D := by noncomm_ring
    _ = rho D * X * (rho_inv D * rho D) * Y * rho_inv D := by rw [h_mid]
    _ = (rho D * X * rho_inv D) * (rho D * Y * rho_inv D) := by noncomm_ring

/-- Full Non-Commutative SLD / Jordan Symmetrized Super-Operator J_ρ(X) = (1/2) * (ρ * X + X * ρ).
    (Note: This is the arithmetic Jordan mean / SLD superoperator, distinct from the BKM integral mean). -/
def sldSymmetrizedSuperOperator (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (rho D * X + X * rho D)

/-- Legacy Alias for Symmetrized Super-Operator. -/
def bkmSymmetrizedSuperOperator (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  sldSymmetrizedSuperOperator D X

/-- Full Non-Commutative SLD Quantum Fisher Candidate Inner Product <A, B>_SLD = Tr(Aᴴ * J_ρ(B)). -/
def fullSLDInnerProduct (A B : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  trace (A.conjTranspose * D.sldSymmetrizedSuperOperator B)

/-- Legacy Alias for Quantum Fisher Candidate Inner Product. -/
def fullBKMInnerProduct (A B : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  fullSLDInnerProduct D A B

/-- **Theorem**: Vanishing Modular Commutator Trace: Tr([ρ, X]) = 0 for any non-commutative operator X. -/
theorem modular_commutator_trace_zero (X : Matrix (Fin n) (Fin n) ℂ) :
    trace (rho D * X - X * rho D) = 0 := by
  rw [trace_sub]
  have h_comm : trace (X * rho D) = trace (rho D * X) := trace_mul_comm X (rho D)
  rw [h_comm, sub_self]

end NonCommutativeDensityOperator

end FullOperatorBKM
