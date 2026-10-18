/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Tactic
import InfoGeometry.QuantumContext.MarkovAttentionGroupInverse
import InfoGeometry.Probability.FiniteWeightedSplitKreinAdjoint

/-!
# Finite Softmax Markov Kernels

For a finite nonempty index type, pairwise real scores define a strictly positive
row-stochastic matrix by row-wise softmax normalization. This owner connects that
matrix to Mathlib's `Matrix.rowStochastic` and the repository's finite group-
inverse and Poisson-solver theorems.

The results are finite algebraic statements. They do not identify a Markov kernel
with a conditional expectation, nor claim convergence of its iterates.
-/

namespace InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel

open Matrix
open scoped BigOperators

noncomputable section

variable {ι : Type*}

/-- Positive Gibbs weight associated to a real score. -/
def gibbsCouplingWeight (scores : ι → ι → ℝ) (i j : ι) : ℝ :=
  Real.exp (scores i j)

theorem gibbsCouplingWeight_pos (scores : ι → ι → ℝ) (i j : ι) :
    0 < gibbsCouplingWeight scores i j :=
  Real.exp_pos (scores i j)

/-- Row partition function for the scores at fixed source index. -/
def queryPartitionFunction [Fintype ι] (scores : ι → ι → ℝ) (i : ι) : ℝ :=
  ∑ j, gibbsCouplingWeight scores i j

theorem queryPartitionFunction_pos [Fintype ι] [Nonempty ι]
    (scores : ι → ι → ℝ) (i : ι) :
    0 < queryPartitionFunction scores i := by
  dsimp [queryPartitionFunction]
  apply Finset.sum_pos'
  · intro j _
    exact le_of_lt (gibbsCouplingWeight_pos scores i j)
  · obtain ⟨j₀⟩ := ‹Nonempty ι›
    exact ⟨j₀, Finset.mem_univ _, gibbsCouplingWeight_pos scores i j₀⟩

/-- Entry of the row-wise softmax transition kernel. -/
def softmaxAttentionKernel [Fintype ι] (scores : ι → ι → ℝ) (i j : ι) : ℝ :=
  gibbsCouplingWeight scores i j / queryPartitionFunction scores i

theorem softmaxAttentionKernel_pos [Fintype ι] [Nonempty ι]
    (scores : ι → ι → ℝ) (i j : ι) :
    0 < softmaxAttentionKernel scores i j :=
  div_pos (gibbsCouplingWeight_pos scores i j) (queryPartitionFunction_pos scores i)

theorem softmaxAttentionKernel_row_sum [Fintype ι] [Nonempty ι]
    (scores : ι → ι → ℝ) (i : ι) :
    ∑ j, softmaxAttentionKernel scores i j = 1 := by
  dsimp [softmaxAttentionKernel]
  have h_ne : queryPartitionFunction scores i ≠ 0 :=
    ne_of_gt (queryPartitionFunction_pos scores i)
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  rw [← div_eq_mul_inv]
  dsimp [queryPartitionFunction]
  exact div_self h_ne

/-- Matrix form of the finite softmax transition kernel. -/
def softmaxAttentionMatrix [Fintype ι] (scores : ι → ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => softmaxAttentionKernel scores i j

@[simp] theorem softmaxAttentionMatrix_apply [Fintype ι]
    (scores : ι → ι → ℝ) (i j : ι) :
    softmaxAttentionMatrix scores i j = softmaxAttentionKernel scores i j :=
  rfl

/-- The score-built softmax matrix is a member of Mathlib's row-stochastic monoid. -/
theorem softmaxAttentionMatrix_mem_rowStochastic [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (scores : ι → ι → ℝ) :
    softmaxAttentionMatrix scores ∈ Matrix.rowStochastic ℝ ι := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  refine ⟨?_, ?_⟩
  · intro i j
    exact le_of_lt (softmaxAttentionKernel_pos scores i j)
  · intro i
    exact softmaxAttentionKernel_row_sum scores i

/-- The Markov Laplacian of a finite softmax score matrix has a group inverse.
This follows from finite row-stochasticity and imposes no irreducibility or
aperiodicity condition. -/
theorem exists_softmaxAttention_laplacian_groupInverse [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (scores : ι → ι → ℝ) :
    ∃ D : Module.End ℝ (ι → ℝ),
      InfoGeometry.Canonical.HartwigSouriauFrameDrazin.IsGroupInverse
        (Matrix.toLin' (1 - softmaxAttentionMatrix scores)) D := by
  exact InfoGeometry.QuantumContext.MarkovDrazin.exists_stochastic_laplacian_groupInverse
    (softmaxAttentionMatrix scores) (softmaxAttentionMatrix_mem_rowStochastic scores)

/-- Every right-hand side in the range of the finite softmax Markov Laplacian
has a unique solution constrained to that range. The group inverse supplies
the solution; this theorem makes no convergence claim about matrix powers. -/
theorem softmaxAttention_poisson_solution_exists_unique
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (scores : ι → ι → ℝ) (b : ι → ℝ)
    (hb : b ∈ (Matrix.toLin' (1 - softmaxAttentionMatrix scores)).range) :
    ∃ D : Module.End ℝ (ι → ℝ),
      InfoGeometry.Canonical.HartwigSouriauFrameDrazin.IsGroupInverse
        (Matrix.toLin' (1 - softmaxAttentionMatrix scores)) D ∧
      Matrix.toLin' (1 - softmaxAttentionMatrix scores) (D b) = b ∧
      D b ∈ (Matrix.toLin' (1 - softmaxAttentionMatrix scores)).range ∧
      ∀ x : ι → ℝ,
        x ∈ (Matrix.toLin' (1 - softmaxAttentionMatrix scores)).range →
        Matrix.toLin' (1 - softmaxAttentionMatrix scores) x = b → x = D b := by
  exact InfoGeometry.QuantumContext.MarkovDrazin.stochastic_laplacian_poisson_solution_exists_unique
    (softmaxAttentionMatrix scores) (softmaxAttentionMatrix_mem_rowStochastic scores) b hb

/-- Any two solutions of the finite softmax Markov Laplacian equation differ
by a constant coordinate. The score matrix is arbitrary; no symmetry
assumption is imposed. -/
theorem softmaxAttention_poisson_solutions_differ_by_const
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (scores : ι → ι → ℝ) (x y : ι → ℝ)
    (hxy : Matrix.toLin'
      (1 - softmaxAttentionMatrix scores) x = Matrix.toLin'
      (1 - softmaxAttentionMatrix scores) y) :
    ∃ c : ℝ, ∀ i, x i - y i = c := by
  apply InfoGeometry.QuantumContext.MarkovDrazin.positive_rowStochastic_laplacian_solutions_differ_by_const
    (softmaxAttentionMatrix scores)
    (softmaxAttentionMatrix_mem_rowStochastic scores)
    (fun i j => by
      rw [softmaxAttentionMatrix_apply]
      exact softmaxAttentionKernel_pos scores i j)
    x y
  simpa only [Matrix.toLin'_apply] using hxy

/-! ### Causal masked softmax -/

The ordinary `softmaxAttentionMatrix` above normalizes over every key. The
following finite kernel instead masks future positions before normalization, so
each row remains stochastic while its support is causal. -/

/-- Unnormalized Gibbs weight, zero outside the autoregressive support `j ≤ i`. -/
def causalGibbsWeight {n : ℕ} (scores : Fin n → Fin n → ℝ)
    (i j : Fin n) : ℝ :=
  if j ≤ i then Real.exp (scores i j) else 0

/-- Row partition function over the present and past positions. -/
def causalPartitionFunction {n : ℕ} (scores : Fin n → Fin n → ℝ)
    (i : Fin n) : ℝ :=
  ∑ j, causalGibbsWeight scores i j

theorem causalPartitionFunction_pos {n : ℕ} (scores : Fin n → Fin n → ℝ)
    (i : Fin n) : 0 < causalPartitionFunction scores i := by
  unfold causalPartitionFunction
  apply Finset.sum_pos'
  · intro j hj
    by_cases hji : j ≤ i
    · simpa [causalGibbsWeight, hji] using
        le_of_lt (Real.exp_pos (scores i j))
    · simp [causalGibbsWeight, hji]
  · refine ⟨i, Finset.mem_univ _, ?_⟩
    simpa [causalGibbsWeight] using Real.exp_pos (scores i i)

/-- Row-normalized softmax restricted to causal keys `j ≤ i`. -/
def causalSoftmaxKernel {n : ℕ} (scores : Fin n → Fin n → ℝ)
    (i j : Fin n) : ℝ :=
  causalGibbsWeight scores i j / causalPartitionFunction scores i

theorem causalSoftmaxKernel_nonneg {n : ℕ} (scores : Fin n → Fin n → ℝ)
    (i j : Fin n) : 0 ≤ causalSoftmaxKernel scores i j := by
  by_cases hji : j ≤ i
  · unfold causalSoftmaxKernel causalGibbsWeight
    simp [hji]
    exact div_nonneg (le_of_lt (Real.exp_pos (scores i j)))
      (le_of_lt (causalPartitionFunction_pos scores i))
  · simp [causalSoftmaxKernel, causalGibbsWeight, hji]

theorem causalSoftmaxKernel_pos_of_allowed {n : ℕ}
    (scores : Fin n → Fin n → ℝ) (i j : Fin n) (hji : j ≤ i) :
    0 < causalSoftmaxKernel scores i j := by
  unfold causalSoftmaxKernel causalGibbsWeight
  simp [hji]
  exact div_pos (Real.exp_pos (scores i j)) (causalPartitionFunction_pos scores i)

theorem causalSoftmaxKernel_eq_zero_of_forbidden {n : ℕ}
    (scores : Fin n → Fin n → ℝ) (i j : Fin n) (hij : i < j) :
    causalSoftmaxKernel scores i j = 0 := by
  have hnot : ¬ j ≤ i := not_le_of_gt hij
  simp [causalSoftmaxKernel, causalGibbsWeight, hnot]

theorem causalSoftmaxKernel_row_sum {n : ℕ}
    (scores : Fin n → Fin n → ℝ) (i : Fin n) :
    ∑ j, causalSoftmaxKernel scores i j = 1 := by
  unfold causalSoftmaxKernel
  have hne : causalPartitionFunction scores i ≠ 0 :=
    ne_of_gt (causalPartitionFunction_pos scores i)
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  rw [← div_eq_mul_inv]
  unfold causalPartitionFunction
  exact div_self hne

/-- Matrix form of the finite autoregressive softmax attention kernel. -/
def causalSoftmaxMatrix {n : ℕ} (scores : Fin n → Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => causalSoftmaxKernel scores i j

@[simp] theorem causalSoftmaxMatrix_apply {n : ℕ}
    (scores : Fin n → Fin n → ℝ) (i j : Fin n) :
    causalSoftmaxMatrix scores i j = causalSoftmaxKernel scores i j := rfl

theorem causalSoftmaxMatrix_mem_rowStochastic {n : ℕ}
    (scores : Fin n → Fin n → ℝ) :
    causalSoftmaxMatrix scores ∈ Matrix.rowStochastic ℝ (Fin n) := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  refine ⟨?_, ?_⟩
  · intro i j
    exact causalSoftmaxKernel_nonneg scores i j
  · intro i
    exact causalSoftmaxKernel_row_sum scores i

theorem causalSoftmaxMatrix_forbidden_entry_zero {n : ℕ}
    (scores : Fin n → Fin n → ℝ) (i j : Fin n) (hij : i < j) :
    causalSoftmaxMatrix scores i j = 0 :=
  causalSoftmaxKernel_eq_zero_of_forbidden scores i j hij

/-- The weighted adjoint of causal softmax has reverse, upper-triangular support. -/
theorem causalSoftmax_weightedAdjoint_forbidden_entry_zero {n : ℕ}
    (π : Fin n → ℝ) (scores : Fin n → Fin n → ℝ) :
    ∀ i j, j < i →
      InfoGeometry.Probability.weightedAdjoint π (causalSoftmaxMatrix scores) i j = 0 := by
  apply InfoGeometry.Probability.weightedAdjoint_lowerTriangular_entry_zero
  intro i j hij
  exact causalSoftmaxMatrix_forbidden_entry_zero scores i j hij

end

end InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel
