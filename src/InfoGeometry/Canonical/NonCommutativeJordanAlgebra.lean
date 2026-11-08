import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Matrix

namespace NonCommutativeJordan

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-- Symmetrized Jordan Product A ∘ B = (1 / 2) • (A * B + B * A) on real matrices. -/
def jordanProduct (A B : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • (A * B + B * A)

/-- Matrix Lie Bracket commutator [A, B] = A * B - B * A on real matrices. -/
def lieBracket (A B : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  A * B - B * A

/-- **Theorem**: Jordan Product Commutativity: A ∘ B = B ∘ A. -/
theorem jordan_product_comm (A B : Matrix (Fin n) (Fin n) ℝ) :
    jordanProduct A B = jordanProduct B A := by
  dsimp [jordanProduct]
  rw [add_comm (A * B) (B * A)]

/-- **Theorem**: Lie Bracket Anti-Symmetry: [A, B] = - [B, A]. -/
theorem lie_bracket_antisymm (A B : Matrix (Fin n) (Fin n) ℝ) :
    lieBracket A B = - lieBracket B A := by
  dsimp [lieBracket]
  rw [neg_sub]

/-- **Theorem**: Jacobi Identity for Matrix Lie Brackets: [A, [B, C]] + [B, [C, A]] + [C, [A, B]] = 0. -/
theorem lie_bracket_jacobi (A B C : Matrix (Fin n) (Fin n) ℝ) :
    lieBracket A (lieBracket B C) + lieBracket B (lieBracket C A) + lieBracket C (lieBracket A B) = 0 := by
  dsimp [lieBracket]
  noncomm_ring

/-- **Theorem**: Jordan Product Trace Equality: Tr(A ∘ B) = Tr(A * B). -/
theorem trace_jordan_product_eq (A B : Matrix (Fin n) (Fin n) ℝ) :
    trace (jordanProduct A B) = trace (A * B) := by
  dsimp [jordanProduct]
  rw [trace_smul, trace_add, smul_eq_mul]
  have h_comm : trace (B * A) = trace (A * B) := trace_mul_comm B A
  rw [h_comm]
  ring

/-- **Theorem**: Vanishing Trace of Matrix Lie Bracket Commutator: Tr([A, B]) = 0. -/
theorem trace_lie_bracket_zero (A B : Matrix (Fin n) (Fin n) ℝ) :
    trace (lieBracket A B) = 0 := by
  dsimp [lieBracket]
  rw [trace_sub]
  have h_comm : trace (B * A) = trace (A * B) := trace_mul_comm B A
  rw [h_comm, sub_self]

end NonCommutativeJordan
