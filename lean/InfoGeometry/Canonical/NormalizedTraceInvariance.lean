import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Field.Basic

set_option linter.unusedSectionVars false

open Matrix

namespace MultiChainNormalizedTrace

variable {t : Type*} [Fintype t] [DecidableEq t] {K : Type*} [Field K]

/-- 1. The Multi-Chain Tensor Algebra Embedding ιₙ : Aₙ → Aₙ₊₁
    Represented as the block diagonal map M ↦ [[M, 0], [0, M]] = M ⊗ I₂ -/
def embeddingMap (M : Matrix t t K) : Matrix (t ⊕ t) (t ⊕ t) K :=
  fromBlocks M 0 0 M

/-- Trace Scaling Relation: Tr(ι(M)) = 2 * Tr(M) -/
theorem embedding_trace (M : Matrix t t K) :
    trace (embeddingMap M) = 2 * trace M := by
  dsimp [trace, embeddingMap]
  rw [Fintype.sum_sum_type]
  simp [fromBlocks]
  ring

/-- 2. Normalized Trace Operator for a matrix space with dimension factor d:
    τ_d(M) = (1 / d) * Tr(M) -/
def normalizedTrace (d : K) (M : Matrix t t K) : K :=
  (1 / d) * trace M

/-- 🏆 THEOREM 1: Normalized Trace Invariance under Tensor Embedding
    Proves that τ_{2d}(ι(M)) = τ_d(M) for any dimension factor d ≠ 0 (char ≠ 2). -/
theorem normalizedTrace_invariance (d : K) (hd : d ≠ 0) (h2 : (2 : K) ≠ 0)
    (M : Matrix t t K) :
    normalizedTrace (2 * d) (embeddingMap M) = normalizedTrace d M := by
  dsimp [normalizedTrace]
  rw [embedding_trace]
  calc 1 / (2 * d) * (2 * trace M)
    _ = (1 / (2 * d) * 2) * trace M := by ring
    _ = (1 / d) * trace M := by
      congr 1
      field_simp [hd, h2]

/-- 3. Level-Indexed Normalized Trace τ_n(M) = (1 / dim_n) * Tr(M) -/
def tau_level (dim_n : K) (M : Matrix t t K) : K :=
  normalizedTrace dim_n M

/-- 🏆 THEOREM 2: Exact Level-Indexed Trace Invariance
    Proves τ_{n+1}(ι(M)) = τ_n(M) where dim_{n+1} = 2 * dim_n. -/
theorem tau_level_invariance (dim_n : K) (hd : dim_n ≠ 0) (h2 : (2 : K) ≠ 0)
    (M : Matrix t t K) :
    tau_level (2 * dim_n) (embeddingMap M) = tau_level dim_n M := by
  exact normalizedTrace_invariance dim_n hd h2 M

end MultiChainNormalizedTrace
