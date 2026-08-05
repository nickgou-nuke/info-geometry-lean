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

namespace UHFDirectLimitCAR

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-- Fermionic Anti-Commutator {A, B} = A * B + B * A on matrix algebra. -/
def antiCommutator (A B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  A * B + B * A

/-- **Theorem**: Anti-Commutator Symmetry: {A, B} = {B, A}. -/
theorem anti_commutator_symmetric (A B : Matrix (Fin n) (Fin n) ℂ) :
    antiCommutator A B = antiCommutator B A := by
  dsimp [antiCommutator]
  rw [add_comm (A * B) (B * A)]

theorem car_identity
    (a aD : Matrix (Fin n) (Fin n) ℂ)
    (h : antiCommutator a aD = 1) :
    a * aD + aD * a = 1 := h

theorem car_sq_zero
    (a : Matrix (Fin n) (Fin n) ℂ)
    (h : antiCommutator a a = 0) :
    a * a = 0 := by
  have h_nil := h
  dsimp [antiCommutator] at h_nil
  have h_double : a * a + a * a = (2 : ℂ) • (a * a) := by
    rw [two_smul]
  rw [h_double] at h_nil
  have h_two_ne : (2 : ℂ) ≠ 0 := by norm_num
  cases smul_eq_zero.mp h_nil with
  | inl h_err => exfalso; exact h_two_ne h_err
  | inr h_res => exact h_res

theorem uhf_embedding_id (X : Matrix (Fin n) (Fin n) ℂ) : X = X := rfl

end UHFDirectLimitCAR
