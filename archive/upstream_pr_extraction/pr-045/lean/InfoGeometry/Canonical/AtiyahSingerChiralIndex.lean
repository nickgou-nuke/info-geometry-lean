import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Matrix Complex

namespace AtiyahSingerIndex

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-- Chiral Dirac Operator Structure with γ⁵ Operator satisfying (γ⁵)² = 1 and {γ⁵, D} = 0. -/
structure ChiralDiracOperator (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] where
  D_val : Matrix (Fin n) (Fin n) ℂ
  gamma5 : Matrix (Fin n) (Fin n) ℂ
  h_gamma5_sq : gamma5 * gamma5 = 1
  h_chiral_anti : gamma5 * D_val + D_val * gamma5 = 0

namespace ChiralDiracOperator

variable (chiral : ChiralDiracOperator n)

/-- **Theorem**: Chiral Gamma5 Involution (γ⁵)² = 1. -/
theorem gamma5_involution : chiral.gamma5 * chiral.gamma5 = 1 :=
  chiral.h_gamma5_sq

/-- **Theorem**: Chiral Dirac Anti-Commutation γ⁵ D = - D γ⁵. -/
theorem chiral_anti_commute : chiral.gamma5 * chiral.D_val = - (chiral.D_val * chiral.gamma5) := by
  have h := chiral.h_chiral_anti
  calc chiral.gamma5 * chiral.D_val
    _ = (chiral.gamma5 * chiral.D_val + chiral.D_val * chiral.gamma5) - chiral.D_val * chiral.gamma5 := by noncomm_ring
    _ = 0 - chiral.D_val * chiral.gamma5 := by rw [h]
    _ = - (chiral.D_val * chiral.gamma5) := by noncomm_ring

/-- McKean-Singer Chiral Trace Index Ind(D) = Tr(γ⁵ * D * D). -/
def mckeanSingerIndex : ℂ :=
  trace (chiral.gamma5 * chiral.D_val * chiral.D_val)

/-- **Theorem**: Vanishing McKean-Singer Index for Chiral Dirac Heat Kernel: Tr(γ⁵ D²) = 0. -/
theorem mckean_singer_index_zero : chiral.mckeanSingerIndex = 0 := by
  dsimp [mckeanSingerIndex]
  have h_comm : trace (chiral.gamma5 * chiral.D_val * chiral.D_val) = trace (chiral.D_val * (chiral.gamma5 * chiral.D_val)) := trace_mul_comm (chiral.gamma5 * chiral.D_val) chiral.D_val
  have h_anti := chiral.chiral_anti_commute
  have h_subst : trace (chiral.D_val * (chiral.gamma5 * chiral.D_val)) = - trace (chiral.D_val * chiral.D_val * chiral.gamma5) := by
    rw [h_anti]
    have h_neg : chiral.D_val * (- (chiral.D_val * chiral.gamma5)) = - (chiral.D_val * chiral.D_val * chiral.gamma5) := by noncomm_ring
    rw [h_neg, trace_neg]
  have h_assoc : chiral.gamma5 * chiral.D_val * chiral.D_val = chiral.gamma5 * (chiral.D_val * chiral.D_val) := by noncomm_ring
  have h_cycle : trace (chiral.D_val * chiral.D_val * chiral.gamma5) = trace (chiral.gamma5 * chiral.D_val * chiral.D_val) := by
    rw [h_assoc]
    exact trace_mul_comm (chiral.D_val * chiral.D_val) chiral.gamma5
  have h_eq : trace (chiral.gamma5 * chiral.D_val * chiral.D_val) = - trace (chiral.gamma5 * chiral.D_val * chiral.D_val) := by
    calc trace (chiral.gamma5 * chiral.D_val * chiral.D_val)
      _ = trace (chiral.D_val * (chiral.gamma5 * chiral.D_val)) := h_comm
      _ = - trace (chiral.D_val * chiral.D_val * chiral.gamma5) := h_subst
      _ = - trace (chiral.gamma5 * chiral.D_val * chiral.D_val) := by rw [h_cycle]
  have h_add : trace (chiral.gamma5 * chiral.D_val * chiral.D_val) + trace (chiral.gamma5 * chiral.D_val * chiral.D_val) = 0 := by
    calc trace (chiral.gamma5 * chiral.D_val * chiral.D_val) + trace (chiral.gamma5 * chiral.D_val * chiral.D_val)
      _ = - trace (chiral.gamma5 * chiral.D_val * chiral.D_val) + trace (chiral.gamma5 * chiral.D_val * chiral.D_val) := by nth_rw 1 [h_eq]
      _ = 0 := by ring
  have h_two : (2 : ℂ) • trace (chiral.gamma5 * chiral.D_val * chiral.D_val) = 0 := by
    rw [two_smul, h_add]
  have h_two_ne : (2 : ℂ) ≠ 0 := by norm_num
  cases smul_eq_zero.mp h_two with
  | inl h_err => exfalso; exact h_two_ne h_err
  | inr h_res => exact h_res

end ChiralDiracOperator

end AtiyahSingerIndex
