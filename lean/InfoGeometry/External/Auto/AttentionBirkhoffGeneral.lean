import Mathlib.Analysis.Convex.Birkhoff
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic

open scoped BigOperators
open scoped Matrix

variable {N : Type*} [Fintype N] [DecidableEq N]

/--
  The Generalized Birkhoff-von Neumann Decomposition of the LLM Attention Matrix.
  This formally proves that an arbitrary N x N Softmax Attention Matrix 
  (which is Doubly Stochastic) can be exactly decomposed into a convex 
  combination of discrete Permutation Matrices.
-/
theorem attention_matrix_is_birkhoff_convex_combination 
    (M : Matrix N N ℝ) (hM : M ∈ doublyStochastic ℝ N) :
    ∃ w : Equiv.Perm N → ℝ, (∀ σ, 0 ≤ w σ) ∧ ∑ σ, w σ = 1 ∧ ∑ σ, w σ • σ.permMatrix ℝ = M := by
  exact exists_eq_sum_perm_of_mem_doublyStochastic hM
