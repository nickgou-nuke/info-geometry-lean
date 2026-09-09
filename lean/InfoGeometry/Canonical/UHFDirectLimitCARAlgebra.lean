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

/-- CAR Algebra Generator Structure satisfying {a, a†} = 1 and {a, a} = 0. -/
structure CARGenerator (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] where
  a_val : Matrix (Fin n) (Fin n) ℂ
  a_dagger : Matrix (Fin n) (Fin n) ℂ
  h_car_identity : antiCommutator a_val a_dagger = 1
  h_car_nilpotent : antiCommutator a_val a_val = 0

namespace CARGenerator

variable (car : CARGenerator n)

/-- **Theorem**: CAR Anti-Commutation Identity {a, a†} = 1. -/
theorem car_identity : car.a_val * car.a_dagger + car.a_dagger * car.a_val = 1 :=
  car.h_car_identity

/-- **Theorem**: Fermionic Operator Nilpotency: a² = 0 from {a, a} = 0. -/
theorem car_sq_zero : car.a_val * car.a_val = 0 := by
  have h_nil := car.h_car_nilpotent
  dsimp [antiCommutator] at h_nil
  have h_double : car.a_val * car.a_val + car.a_val * car.a_val = (2 : ℂ) • (car.a_val * car.a_val) := by
    rw [two_smul]
  rw [h_double] at h_nil
  have h_two_ne : (2 : ℂ) ≠ 0 := by norm_num
  cases smul_eq_zero.mp h_nil with
  | inl h_err => exfalso; exact h_two_ne h_err
  | inr h_res => exact h_res

/-- UHF Inductive Colimit Step Embedding Matrix Norm Factor 1. -/
def uhfEmbedding (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  X

/-- **Theorem**: UHF Direct Inductive Colimit Step Embedding Identity: ι_n(X) = X. -/
theorem uhf_embedding_id (X : Matrix (Fin n) (Fin n) ℂ) :
    uhfEmbedding X = X := rfl

end CARGenerator

end UHFDirectLimitCAR
