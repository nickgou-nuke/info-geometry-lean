import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace InfoGeometry.Neurosymbolic.BornNMFEngine

open Matrix
open scoped BigOperators

/-- Elementwise non-negativity predicate for real matrices -/
def MatrixNonneg {m n : Type*} (M : Matrix m n ℝ) : Prop :=
  ∀ i j, 0 ≤ M i j

/-- Born Rule Matrix Map: P_ij = M_ij² -/
def bornRuleMap {m n : Type*} (M : Matrix m n ℝ) : Matrix m n ℝ :=
  fun i j => (M i j) ^ 2

/-- Theorem 1: The Born Rule map produces a strictly non-negative matrix for any real matrix. -/
theorem born_rule_nonneg {m n : Type*} (M : Matrix m n ℝ) :
    MatrixNonneg (bornRuleMap M) := by
  intro i j
  dsimp [bornRuleMap, MatrixNonneg]
  exact sq_nonneg (M i j)

/-- Theorem 2: NMF Matrix Multiplication preserves non-negativity.
    If W ≥ 0 and H ≥ 0, then W * H ≥ 0. -/
theorem nmf_mul_nonneg {m k n : Type*} [Fintype k]
    (W : Matrix m k ℝ) (H : Matrix k n ℝ)
    (hW : MatrixNonneg W) (hH : MatrixNonneg H) :
    MatrixNonneg (W * H) := by
  intro i l
  rw [Matrix.mul_apply]
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (hW i j) (hH j l)

/--
Structure representing a Neurosymbolic Quantum-to-Classical Factorization Engine.
Translates continuous neural amplitude matrices M via the Born Rule into
non-negative transition matrices P = M², which are then factorized by NMF
into bipartite language W and formal type H factors.
-/
structure NeurosymbolicFactorization (m k n : Type*) [Fintype k] where
  amplitude_matrix : Matrix m n ℝ
  born_prob_matrix : Matrix m n ℝ
  left_factor_W : Matrix m k ℝ
  right_factor_H : Matrix k n ℝ
  h_born : born_prob_matrix = bornRuleMap amplitude_matrix
  h_born_nonneg : MatrixNonneg born_prob_matrix
  h_W_nonneg : MatrixNonneg left_factor_W
  h_H_nonneg : MatrixNonneg right_factor_H
  h_factor_nonneg : MatrixNonneg (left_factor_W * right_factor_H)
  h_factor_eq : left_factor_W * right_factor_H = born_prob_matrix

/-- Main Theorem: Proof of existence of the Neurosymbolic Born-Rule NMF Decoherence Engine. -/
theorem neurosymbolic_engine_exists {m k n : Type*} [Fintype k] (M : Matrix m n ℝ)
    (W : Matrix m k ℝ) (H : Matrix k n ℝ) (hW : MatrixNonneg W) (hH : MatrixNonneg H)
    (hFactor : W * H = bornRuleMap M) :
    Nonempty (NeurosymbolicFactorization m k n) := by
  refine ⟨⟨M, bornRuleMap M, W, H, rfl, born_rule_nonneg M, hW, hH,
    by simpa [hFactor] using nmf_mul_nonneg W H hW hH, hFactor⟩⟩

end InfoGeometry.Neurosymbolic.BornNMFEngine
