import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Module.Basic

set_option linter.unusedSectionVars false

open Matrix

namespace MultiChainUHF

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- 1. The Multi-Chain Tensor Algebra Embedding ιₙ : Aₙ → Aₙ₊₁
    Represented as the block diagonal map M ↦ [[M, 0], [0, M]] = M ⊗ I₂ -/
def embeddingMap (M : Matrix n n R) : Matrix (n ⊕ n) (n ⊕ n) R :=
  fromBlocks M 0 0 M

/-- Preservation of Matrix Multiplication: ι(M * N) = ι(M) * ι(N) -/
theorem embedding_mul (M N : Matrix n n R) :
    embeddingMap (M * N) = embeddingMap M * embeddingMap N := by
  dsimp [embeddingMap]
  rw [fromBlocks_multiply]
  simp

/-- Preservation of Identity: ι(I) = I -/
theorem embedding_one :
    embeddingMap (1 : Matrix n n R) = 1 := by
  dsimp [embeddingMap]
  ext (i | i) (j | j) <;> simp [fromBlocks, Matrix.one_apply]

/-- Linearity - Preservation of Addition: ι(M + N) = ι(M) + ι(N) -/
theorem embedding_add (M N : Matrix n n R) :
    embeddingMap (M + N) = embeddingMap M + embeddingMap N := by
  ext (i | i) (j | j) <;> simp [embeddingMap, fromBlocks]

/-- Injectivity of the Embedding Map (Kernel is trivial) -/
theorem embedding_injective : Function.Injective (embeddingMap (n := n) (R := R)) := by
  intro M N h
  ext i j
  have h_block := congrFun (congrFun h (Sum.inl i)) (Sum.inl j)
  dsimp [embeddingMap, fromBlocks] at h_block
  exact h_block

/-- Trace Scaling Relation: Tr(ι(M)) = 2 * Tr(M) -/
theorem embedding_trace (M : Matrix n n R) :
    trace (embeddingMap M) = 2 * trace M := by
  dsimp [trace, embeddingMap]
  rw [Fintype.sum_sum_type]
  simp [fromBlocks]
  ring

end MultiChainUHF
