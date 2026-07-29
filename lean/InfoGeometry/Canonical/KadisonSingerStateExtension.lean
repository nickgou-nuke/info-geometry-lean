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

namespace KadisonSingerState

variable {n : ℕ} [DecidableEq (Fin n)]

/-- C*-Algebra Density State Functional ω(A) = Tr(ρ * A) with Tr(ρ) = 1. -/
structure CStarState (n : ℕ) [DecidableEq (Fin n)] where
  rho : selfAdjoint (Matrix (Fin n) (Fin n) ℂ)
  h_rho_normalized : trace (rho : Matrix (Fin n) (Fin n) ℂ) = 1

namespace CStarState

variable (state : CStarState n)

def rhoVal : Matrix (Fin n) (Fin n) ℂ := state.rho

theorem rho_self_adj : (rhoVal state).conjTranspose = rhoVal state := by
  simpa only [rhoVal, Matrix.star_eq_conjTranspose] using state.rho.property

/-- State Evaluation Functional ω(A) = Tr(ρ * A). -/
def apply (A : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  trace (rhoVal state * A)

/-- **Theorem**: State Evaluation Normalization: ω(1) = 1. -/
theorem state_normalized : state.apply 1 = 1 := by
  dsimp [apply]
  rw [mul_one, state.h_rho_normalized]

/-- **Theorem**: State Functional Linearity under Matrix Addition: ω(A + B) = ω(A) + ω(B). -/
theorem state_add (A B : Matrix (Fin n) (Fin n) ℂ) :
    state.apply (A + B) = state.apply A + state.apply B := by
  dsimp [apply]
  rw [mul_add, trace_add]

/-- **Theorem**: State Functional Linearity under Scalar Multiplication: ω(c • A) = c * ω(A). -/
theorem state_smul (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    state.apply (c • A) = c * state.apply A := by
  dsimp [apply]
  rw [Matrix.mul_smul, trace_smul, smul_eq_mul]

/-- Tracial State Structure where ρ = (1/n) • 1. -/
def tracialState (h_n : (n : ℂ) ≠ 0) : CStarState n where
  rho := ⟨(1 / (n : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ), by
    rw [conjTranspose_smul, conjTranspose_one]
    simp⟩
  h_rho_normalized := by
    rw [trace_smul, trace_one, Fintype.card_fin]
    dsimp [nsmul_eq_mul]
    rw [div_mul_cancel₀ 1 h_n]

/-- **Theorem**: Tracial State Commutativity ω([A, B]) = 0 for ρ = (1/n) • 1. -/
theorem tracial_state_commutator_zero (h_n : (n : ℂ) ≠ 0) (A B : Matrix (Fin n) (Fin n) ℂ) :
    (tracialState h_n).apply (A * B - B * A) = 0 := by
  dsimp [tracialState, apply]
  have h_smul : ((1 / (n : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ)) * (A * B - B * A) = (1 / (n : ℂ)) • (A * B - B * A) := by
    rw [Matrix.smul_mul, one_mul]
  rw [h_smul, trace_smul, trace_sub]
  have h_tr_comm : trace (A * B) = trace (B * A) := trace_mul_comm A B
  rw [h_tr_comm, sub_self, smul_zero]

end CStarState

end KadisonSingerState
