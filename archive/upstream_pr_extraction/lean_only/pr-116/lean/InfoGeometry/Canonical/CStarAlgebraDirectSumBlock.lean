import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Matrix Complex

namespace CStarBlockAlgebra

variable {n m : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)] [Fintype (Fin m)] [DecidableEq (Fin m)]

/-- C*-Algebra Direct Sum Block Operator A ⊕ B = fromBlocks A 0 0 B. -/
def directSumBlock (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℂ :=
  fromBlocks A 0 0 B

/-- **Theorem**: Block Operator Conjugate Transpose Involution (A ⊕ B)† = A† ⊕ B†. -/
theorem direct_sum_block_conj_transpose (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin m) (Fin m) ℂ) :
    (directSumBlock A B).conjTranspose = directSumBlock A.conjTranspose B.conjTranspose := by
  dsimp [directSumBlock]
  rw [fromBlocks_conjTranspose]
  simp

/-- **Theorem**: Block Operator Multiplication Homomorphism (A₁ ⊕ B₁) * (A₂ ⊕ B₂) = (A₁ A₂) ⊕ (B₁ B₂). -/
theorem direct_sum_block_mul (A1 A2 : Matrix (Fin n) (Fin n) ℂ) (B1 B2 : Matrix (Fin m) (Fin m) ℂ) :
    directSumBlock A1 B1 * directSumBlock A2 B2 = directSumBlock (A1 * A2) (B1 * B2) := by
  dsimp [directSumBlock]
  rw [fromBlocks_multiply]
  simp

/-- **Theorem**: Block Operator Trace Additivity Tr(A ⊕ B) = Tr(A) + Tr(B). -/
theorem direct_sum_block_trace (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin m) (Fin m) ℂ) :
    trace (directSumBlock A B) = trace A + trace B := by
  dsimp [directSumBlock, trace]
  rw [Fintype.sum_sum_type]
  congr 1

end CStarBlockAlgebra
