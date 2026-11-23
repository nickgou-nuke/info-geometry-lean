/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

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

variable {R : Type*} [Ring R] [Nontrivial R]

def _witness_a_44_R : Matrix (Fin 4) (Fin 4) R := Matrix.single 0 1 1
def _witness_b_44_R : Matrix (Fin 4) (Fin 4) R := Matrix.single 1 0 1

theorem _witness_noncommute_44_R {R : Type*} [Ring R] [Nontrivial R] :
    _witness_a_44_R (R := R) * _witness_b_44_R (R := R) ≠
      _witness_b_44_R (R := R) * _witness_a_44_R (R := R) := by
  intro h
  have h₁ : _witness_a_44_R (R := R) * _witness_b_44_R (R := R) =
      Matrix.single 0 0 (1 : R) := by
    simp [_witness_a_44_R, _witness_b_44_R, Matrix.single_mul_single_same]
  have h₂ : _witness_b_44_R (R := R) * _witness_a_44_R (R := R) =
      Matrix.single 1 1 (1 : R) := by
    simp [_witness_a_44_R, _witness_b_44_R, Matrix.single_mul_single_same]
  rw [h₁, h₂] at h
  have h₃ := congrFun (congrFun h 0) 0
  norm_num at h₃

/-!
# Finite Softmax Markov Kernels

For a finite nonempty index type, pairwise real scores define a strictly positive
row-stochastic matrix by row-wise softmax normalization. This owner connects that
matrix to Mathlib's `Matrix.rowStochastic` and the repository's finite group-
inverse and Poisson-solver theorems.

The results are finite algebraic statements. They do not identify a Markov kernel
with a conditional expectation, nor claim convergence of its iterates.

## BUCKET 1: Kernel-verified finite statements
Softmax positivity, row normalization, causal support, and finite matrix
identities are proved for the explicitly defined carriers.

## BUCKET 2: Conditional Markov consequences
Group-inverse and Poisson-solver results use the finite stochasticity and range
hypotheses stated in their theorem contracts.

## BUCKET 3: Analytic and model-level claims outside this owner
No infinite-time convergence or full-Transformer attention-sink claim is made.
-/

namespace InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel

open Matrix
open scoped BigOperators

noncomputable section

variable {ι : Type*}

/-- Positive Gibbs weight associated to a real score. -/
def gibbsCouplingWeight (scores : ι → ι → ℝ) (i j : ι) : ℝ :=
  Real.exp (scores i j)

/-- Every real score has a strictly positive exponential Gibbs weight. -/
theorem gibbsCouplingWeight_pos (scores : ι → ι → ℝ) (i j : ι) :
    0 < gibbsCouplingWeight scores i j := by
  unfold gibbsCouplingWeight
  positivity

/-- Row partition function for the scores at fixed source index. -/
def queryPartitionFunction [Fintype ι] (scores : ι → ι → ℝ) (i : ι) : ℝ :=
  ∑ j, gibbsCouplingWeight scores i j

/-- The finite row partition function is strictly positive on a nonempty index
type, since it is a finite sum of positive Gibbs weights. -/
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

/-- Every entry of an unmasked finite softmax kernel is strictly positive. -/
theorem softmaxAttentionKernel_pos [Fintype ι] [Nonempty ι]
    (scores : ι → ι → ℝ) (i j : ι) :
    0 < softmaxAttentionKernel scores i j := by
  unfold softmaxAttentionKernel gibbsCouplingWeight
  exact div_pos (Real.exp_pos (scores i j)) (queryPartitionFunction_pos scores i)

/-- Each row of the unmasked finite softmax kernel sums to one. -/
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
      change 0 < softmaxAttentionKernel scores i j
      exact softmaxAttentionKernel_pos scores i j)
    x y
  simpa only [Matrix.toLin'_apply] using hxy

/-! ### Causal masked softmax

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

/-- The causal partition function is positive because the diagonal position is
always an allowed key and contributes a positive exponential term. -/
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

/-- Causal softmax entries are nonnegative, including the masked zero entries. -/
theorem causalSoftmaxKernel_nonneg {n : ℕ} (scores : Fin n → Fin n → ℝ)
    (i j : Fin n) : 0 ≤ causalSoftmaxKernel scores i j := by
  by_cases hji : j ≤ i
  · unfold causalSoftmaxKernel causalGibbsWeight
    simp [hji]
    exact div_nonneg (le_of_lt (Real.exp_pos (scores i j)))
      (le_of_lt (causalPartitionFunction_pos scores i))
  · simp [causalSoftmaxKernel, causalGibbsWeight, hji]

/-- Every allowed causal key receives strictly positive normalized weight. -/
theorem causalSoftmaxKernel_pos_of_allowed {n : ℕ}
    (scores : Fin n → Fin n → ℝ) (i j : Fin n) (hji : j ≤ i) :
    0 < causalSoftmaxKernel scores i j := by
  unfold causalSoftmaxKernel causalGibbsWeight
  simp [hji]
  exact div_pos (Real.exp_pos (scores i j)) (causalPartitionFunction_pos scores i)

/-- A key strictly to the future has zero causal-softmax weight. -/
theorem causalSoftmaxKernel_eq_zero_of_forbidden {n : ℕ}
    (scores : Fin n → Fin n → ℝ) (i j : Fin n) (hij : i < j) :
    causalSoftmaxKernel scores i j = 0 := by
  have hnot : ¬ j ≤ i := not_le_of_gt hij
  simp [causalSoftmaxKernel, causalGibbsWeight, hnot]

/-- The masked causal-softmax weights still sum to one in every row. -/
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

/-- If a causal row has only one allowed key, its normalized mass is exactly
one at that key. This isolates the boundary-row fact without asserting that
deeper causal-softmax rows have zero diagonal mass. -/
theorem causalSoftmaxKernel_singleton_row {n : ℕ}
    (scores : Fin n → Fin n → ℝ) (i : Fin n)
    (h_single : ∀ j : Fin n, j ≤ i → j = i) (j : Fin n) :
    causalSoftmaxKernel scores i j = if j = i then 1 else 0 := by
  by_cases hji : j ≤ i
  · have hji' : j = i := h_single j hji
    subst j
    unfold causalSoftmaxKernel causalGibbsWeight
    have hpart : causalPartitionFunction scores i = Real.exp (scores i i) := by
      unfold causalPartitionFunction
      rw [Finset.sum_eq_single i]
      · simp [causalGibbsWeight]
      · intro k hk hki
        have hnot : ¬ k ≤ i := by
          intro h
          exact hki (h_single k h)
        simp [causalGibbsWeight, hnot]
      · simp
    rw [hpart]
    simp
  · have hij : i < j := lt_of_not_ge hji
    rw [causalSoftmaxKernel_eq_zero_of_forbidden scores i j hij]
    simp [ne_of_gt hij]

/-- Matrix form of the finite autoregressive softmax attention kernel. -/
def causalSoftmaxMatrix {n : ℕ} (scores : Fin n → Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => causalSoftmaxKernel scores i j

def _witness_a : Matrix (Fin 2) (Fin 2) ℝ := Matrix.single 0 1 1
def _witness_b : Matrix (Fin 2) (Fin 2) ℝ := Matrix.single 1 0 1

theorem _witness_noncommute : _witness_a * _witness_b ≠ _witness_b * _witness_a := by
  intro h
  have h₁ : _witness_a * _witness_b = Matrix.single 0 0 (1 : ℝ) := by
    simp [_witness_a, _witness_b, Matrix.single_mul_single_same]
  have h₂ : _witness_b * _witness_a = Matrix.single 1 1 (1 : ℝ) := by
    simp [_witness_a, _witness_b, Matrix.single_mul_single_same]
  rw [h₁, h₂] at h
  have h₃ := congrFun (congrFun h 0) 0
  norm_num at h₃

/-- The first row of causal softmax is the point mass at the first token.
This follows from the causal support condition: at index zero, no other key is
allowed. The statement concerns this finite normalized kernel only; it makes
no claim about attention-sink behavior in a full Transformer. -/
theorem causalSoftmaxMatrix_first_row {n : ℕ} (hn : 0 < n)
    (scores : Fin n → Fin n → ℝ) (j : Fin n) :
    causalSoftmaxMatrix scores ⟨0, hn⟩ j = if j.val = 0 then 1 else 0 := by
  have h_single : ∀ k : Fin n, k ≤ (⟨0, hn⟩ : Fin n) → k = ⟨0, hn⟩ := by
    intro k hk
    apply Fin.ext
    exact Nat.eq_zero_of_le_zero (Fin.le_iff_val_le_val.mp hk)
  change causalSoftmaxKernel scores ⟨0, hn⟩ j = if j.val = 0 then 1 else 0
  rw [causalSoftmaxKernel_singleton_row scores ⟨0, hn⟩ h_single]
  by_cases hj : j.val = 0
  · have hji : j = (⟨0, hn⟩ : Fin n) := Fin.ext hj
    simp [hji]
  · have hnot : j ≠ (⟨0, hn⟩ : Fin n) := by
      intro h
      exact hj (congrArg Fin.val h)
    simp [hnot, hj]

/-- The causal-softmax boundary row remains the token-zero point mass under
every natural power. This is an absorbing-row statement; it does not imply
that the whole matrix converges to a rank-one sink. -/
theorem causalSoftmaxMatrix_pow_first_row {n : ℕ} (hn : 0 < n)
    (scores : Fin n → Fin n → ℝ) (k : ℕ) (j : Fin n) :
    (causalSoftmaxMatrix scores ^ k) ⟨0, hn⟩ j = if j.val = 0 then 1 else 0 := by
  induction k generalizing j with
  | zero =>
      by_cases hj : j.val = 0
      · have hj' : j = (⟨0, hn⟩ : Fin n) := Fin.ext hj
        subst j
        simp
      · have hne : (⟨0, hn⟩ : Fin n) ≠ j := by
          intro h
          apply hj
          have hv := congrArg Fin.val h
          simpa using hv.symm
        simp [hne]
        exact hj
  | succ k ih =>
      rw [pow_succ, Matrix.mul_apply]
      by_cases hj : j.val = 0
      · have hj' : j = (⟨0, hn⟩ : Fin n) := Fin.ext hj
        subst j
        rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
        · simp [ih, causalSoftmaxMatrix_first_row]
        · intro b hb hne
          have hb0 : b.val ≠ 0 := by
            intro h
            apply hne
            exact Fin.ext h
          simp [ih b, hb0]
        · simp
      · rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
        · simp [ih, causalSoftmaxMatrix_first_row, hj]
        · intro b hb hne
          have hb0 : b.val ≠ 0 := by
            intro h
            apply hne
            exact Fin.ext h
          simp [ih b, hb0]
        · simp

/-- In a distinct strict-past model, if every row is stochastic, token zero is
absorbing, and the remaining diagonal entries vanish, then three transitions
collapse to the token-zero kernel. The claim is stated on Mathlib's finite
matrix carrier and is separate from ordinary causal softmax. -/
theorem strictPastMarkovMatrix4_cube_eq_token0Sink
    {R : Type*} [CommRing R] (a20 a21 a30 a31 a32 : R)
    (h_row2 : a20 + a21 = 1) (h_row3 : a30 + a31 + a32 = 1) :
    let A : Matrix (Fin 4) (Fin 4) R :=
      !![1, 0, 0, 0;
        1, 0, 0, 0;
        a20, a21, 0, 0;
        a30, a31, a32, 0]
    let S : Matrix (Fin 4) (Fin 4) R :=
      !![1, 0, 0, 0;
        1, 0, 0, 0;
        1, 0, 0, 0;
        1, 0, 0, 0]
    A * A * A = S := by
  dsimp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals try assumption
  all_goals linear_combination h_row3 + a32 * h_row2

/-- Once a strict-past four-state chain has reached the token-zero sink after
three transitions, every later power remains at that sink. This is a finite
four-state statement; ordinary causal softmax is excluded because its
self-attention diagonal is strictly positive. -/
theorem strictPastMarkovMatrix4_pow_eq_token0Sink
    {R : Type*} [CommRing R] (a20 a21 a30 a31 a32 : R)
    (h_row2 : a20 + a21 = 1) (h_row3 : a30 + a31 + a32 = 1)
    (k : ℕ) (hk : 3 ≤ k) :
    (let A : Matrix (Fin 4) (Fin 4) R :=
      !![1, 0, 0, 0;
        1, 0, 0, 0;
        a20, a21, 0, 0;
        a30, a31, a32, 0]
     let S : Matrix (Fin 4) (Fin 4) R :=
      !![1, 0, 0, 0;
        1, 0, 0, 0;
        1, 0, 0, 0;
        1, 0, 0, 0]
     A ^ k = S) := by
  dsimp
  let A : Matrix (Fin 4) (Fin 4) R :=
    !![1, 0, 0, 0;
      1, 0, 0, 0;
      a20, a21, 0, 0;
      a30, a31, a32, 0]
  let S : Matrix (Fin 4) (Fin 4) R :=
    !![1, 0, 0, 0;
      1, 0, 0, 0;
      1, 0, 0, 0;
      1, 0, 0, 0]
  have hCube : A * A * A = S := by
    simpa [A, S] using
      strictPastMarkovMatrix4_cube_eq_token0Sink
        a20 a21 a30 a31 a32 h_row2 h_row3
  have hSinkStep : S * A = S := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, S, Matrix.mul_apply, Fin.sum_univ_succ]
  have hpow : ∀ n : ℕ, A ^ (3 + n) = S := by
    intro n
    induction n with
    | zero => simpa [pow_succ, pow_two] using hCube
    | succ n ih =>
        calc
          A ^ (3 + (n + 1)) = A ^ (3 + n) * A := by
            rw [Nat.add_succ, pow_succ]
          _ = S * A := by rw [ih]
          _ = S := hSinkStep
  have hk' : 3 + (k - 3) = k := by omega
  rw [← hk']
  exact hpow (k - 3)

/-- Every strictly lower-triangular four-state matrix is nilpotent of index at
most four, over an arbitrary possibly noncommutative ring. -/
theorem strictLowerMatrix4_fourth_power_eq_zero
    {R : Type*} [Ring R] (x10 x20 x21 x30 x31 x32 : R) :
    let N : Matrix (Fin 4) (Fin 4) R :=
      !![0, 0, 0, 0;
        x10, 0, 0, 0;
        x20, x21, 0, 0;
        x30, x31, x32, 0]
    N * N * N * N = 0 := by
  dsimp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

/-- Two-sided geometric inverse for `1 + q` when `q⁴ = 0`; no commutativity
assumption is used. -/
theorem one_add_fourth_nilpotent_two_sided_inverse
    {R : Type*} [Ring R] (q : R) (hq : q * q * q * q = 0) :
    (1 + q) * (1 - q + q * q - q * q * q) = 1 ∧
    (1 - q + q * q - q * q * q) * (1 + q) = 1 := by
  constructor
  · calc
      (1 + q) * (1 - q + q * q - q * q * q) = 1 - q * q * q * q := by
        noncomm_ring
      _ = 1 := by rw [hq]; simp
  · calc
      (1 - q + q * q - q * q * q) * (1 + q) = 1 - q * q * q * q := by
        noncomm_ring
      _ = 1 := by rw [hq]; simp

/-- Exact two-sided inverse for a four-state lower-triangular operator whose
diagonal entries are units. The proof factors on both sides by the diagonal
inverse and applies the finite nilpotent geometric inverse to the resulting
strictly lower-triangular remainder. -/
theorem lowerTriangularMatrix4_diagonalUnits_inverse
    {R : Type*} [Ring R]
    (d0 d1 d2 d3 u0 u1 u2 u3 : R)
    (x10 x20 x21 x30 x31 x32 : R)
    (h0r : d0 * u0 = 1) (h1r : d1 * u1 = 1)
    (h2r : d2 * u2 = 1) (h3r : d3 * u3 = 1)
    (h0l : u0 * d0 = 1) (h1l : u1 * d1 = 1)
    (h2l : u2 * d2 = 1) (h3l : u3 * d3 = 1) :
    let M : Matrix (Fin 4) (Fin 4) R :=
      !![d0, 0, 0, 0;
        x10, d1, 0, 0;
        x20, x21, d2, 0;
        x30, x31, x32, d3]
    let U : Matrix (Fin 4) (Fin 4) R :=
      !![u0, 0, 0, 0;
        0, u1, 0, 0;
        0, 0, u2, 0;
        0, 0, 0, u3]
    let Q : Matrix (Fin 4) (Fin 4) R :=
      !![0, 0, 0, 0;
        x10 * u0, 0, 0, 0;
        x20 * u0, x21 * u1, 0, 0;
        x30 * u0, x31 * u1, x32 * u2, 0]
    let geomRight : Matrix (Fin 4) (Fin 4) R := 1 - Q + Q * Q - Q * Q * Q
    M * (U * geomRight) = 1 ∧ (U * geomRight) * M = 1 := by
  dsimp
  let M : Matrix (Fin 4) (Fin 4) R :=
    !![d0, 0, 0, 0; x10, d1, 0, 0; x20, x21, d2, 0; x30, x31, x32, d3]
  let U : Matrix (Fin 4) (Fin 4) R :=
    !![u0, 0, 0, 0; 0, u1, 0, 0; 0, 0, u2, 0; 0, 0, 0, u3]
  let Q : Matrix (Fin 4) (Fin 4) R :=
    !![0, 0, 0, 0; x10*u0, 0, 0, 0; x20*u0, x21*u1, 0, 0;
      x30*u0, x31*u1, x32*u2, 0]
  let qLeft : Matrix (Fin 4) (Fin 4) R :=
    !![0, 0, 0, 0; u1*x10, 0, 0, 0; u2*x20, u2*x21, 0, 0;
      u3*x30, u3*x31, u3*x32, 0]
  let geomRight : Matrix (Fin 4) (Fin 4) R := 1 - Q + Q * Q - Q * Q * Q
  let geomLeft : Matrix (Fin 4) (Fin 4) R := 1 - qLeft + qLeft * qLeft - qLeft * qLeft * qLeft
  have hMU : M * U = 1 + Q := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, U, Q, Matrix.mul_apply,
        Fin.sum_univ_succ, h0r, h1r, h2r, h3r]
  have hUM : U * M = 1 + qLeft := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, U, qLeft, Matrix.mul_apply,
        Fin.sum_univ_succ, h0l, h1l, h2l, h3l]
  have hQ4 : Q * Q * Q * Q = 0 := by
    simpa [Q] using strictLowerMatrix4_fourth_power_eq_zero
      (x10 * u0) (x20 * u0) (x21 * u1) (x30 * u0) (x31 * u1) (x32 * u2)
  have hQL4 : qLeft * qLeft * qLeft * qLeft = 0 := by
    simpa [qLeft] using strictLowerMatrix4_fourth_power_eq_zero
      (u1 * x10) (u2 * x20) (u2 * x21) (u3 * x30) (u3 * x31) (u3 * x32)
  have hGR := one_add_fourth_nilpotent_two_sided_inverse Q hQ4
  have hGL := one_add_fourth_nilpotent_two_sided_inverse qLeft hQL4
  have hRight : M * (U * geomRight) = 1 := by
    calc
      M * (U * geomRight) = (M * U) * geomRight := by rw [mul_assoc]
      _ = (1 + Q) * geomRight := by rw [hMU]
      _ = 1 := hGR.1
  have hLeft : (geomLeft * U) * M = 1 := by
    calc
      (geomLeft * U) * M = geomLeft * (U * M) := by rw [mul_assoc]
      _ = geomLeft * (1 + qLeft) := by rw [hUM]
      _ = 1 := hGL.2
  have hInv : geomLeft * U = U * geomRight := by
    calc
      geomLeft * U = (geomLeft * U) * 1 := by simp
      _ = (geomLeft * U) * (M * (U * geomRight)) := by rw [hRight]
      _ = ((geomLeft * U) * M) * (U * geomRight) := by simp [mul_assoc]
      _ = 1 * (U * geomRight) := by rw [hLeft]
      _ = U * geomRight := by simp
  exact ⟨hRight, by rw [← hInv]; exact hLeft⟩

/-- Every causal-softmax row assigns strictly positive probability to its own
token, since the diagonal key is always in the allowed support. Thus the
strict-past, zero-diagonal hypothesis used in some finite Markov-chain sink
models is not satisfied by this ordinary finite softmax kernel. -/
theorem causalSoftmaxMatrix_diagonal_pos {n : ℕ}
    (scores : Fin n → Fin n → ℝ) (i : Fin n) :
    0 < causalSoftmaxMatrix scores i i := by
  change 0 < causalSoftmaxKernel scores i i
  exact causalSoftmaxKernel_pos_of_allowed scores i i (le_refl i)

/-- Every natural power of a nonempty finite causal-softmax matrix retains a
strictly positive diagonal. The positive self-loop at `i` contributes a
positive summand at each multiplication step, while all other summands are
nonnegative. -/
theorem causalSoftmaxMatrix_pow_diagonal_pos {n : ℕ}
    (scores : Fin n → Fin n → ℝ) (k : ℕ) (i : Fin n) :
    0 < (causalSoftmaxMatrix scores ^ k) i i := by
  have hA : ∀ j l, 0 ≤ causalSoftmaxMatrix scores j l := by
    intro j l
    exact causalSoftmaxKernel_nonneg scores j l
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_pos'
      · intro j _
        exact mul_nonneg (Matrix.pow_apply_nonneg hA k i j) (hA j i)
      · exact ⟨i, Finset.mem_univ _,
          mul_pos ih (causalSoftmaxMatrix_diagonal_pos scores i)⟩

/-- Ordinary causal softmax cannot have all diagonal entries zero when the
sequence is nonempty. This distinguishes its positive self-attention weights
from the additional strict-past assumption that yields finite-time sink
collapse in a separate triangular Markov model. -/
theorem causalSoftmaxMatrix_not_strictPast {n : ℕ} (hn : 0 < n)
    (scores : Fin n → Fin n → ℝ) :
    ¬ (∀ i : Fin n, causalSoftmaxMatrix scores i i = 0) := by
  intro hzero
  have hpos := causalSoftmaxMatrix_diagonal_pos scores ⟨0, hn⟩
  rw [hzero ⟨0, hn⟩] at hpos
  exact (lt_irrefl 0) hpos

/-- The causal-softmax matrix is row-stochastic: entries are nonnegative and
each row has total mass one. -/
theorem causalSoftmaxMatrix_mem_rowStochastic {n : ℕ}
    (scores : Fin n → Fin n → ℝ) :
    causalSoftmaxMatrix scores ∈ Matrix.rowStochastic ℝ (Fin n) := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  refine ⟨?_, ?_⟩
  · intro i j
    exact causalSoftmaxKernel_nonneg scores i j
  · intro i
    exact causalSoftmaxKernel_row_sum scores i

/-- The causal-softmax matrix is lower triangular: entries strictly above the
diagonal vanish because their key positions are forbidden by the causal mask. -/
theorem causalSoftmaxMatrix_lowerTriangular {n : ℕ}
    (scores : Fin n → Fin n → ℝ) :
    Matrix.BlockTriangular (causalSoftmaxMatrix scores) ⇑OrderDual.toDual := by
  intro i j hij
  change i < j at hij
  change causalSoftmaxKernel scores i j = 0
  exact causalSoftmaxKernel_eq_zero_of_forbidden scores i j hij

/-- The determinant of finite causal softmax is strictly positive. It is the
product of its strictly positive diagonal self-attention weights. -/
theorem causalSoftmaxMatrix_det_pos {n : ℕ}
    (scores : Fin n → Fin n → ℝ) :
    0 < Matrix.det (causalSoftmaxMatrix scores) := by
  rw [Matrix.det_of_isLowerTriangular (causalSoftmaxMatrix scores)
    (causalSoftmaxMatrix_lowerTriangular scores)]
  apply Finset.prod_pos
  intro i hi
  exact causalSoftmaxMatrix_diagonal_pos scores i

/-- Every finite causal-softmax matrix is a unit. Thus its finite powers are
also invertible; the point-mass first row does not imply rank-one collapse of
the whole matrix. -/
theorem causalSoftmaxMatrix_isUnit {n : ℕ}
    (scores : Fin n → Fin n → ℝ) :
    IsUnit (causalSoftmaxMatrix scores) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  exact isUnit_iff_ne_zero.mpr (ne_of_gt (causalSoftmaxMatrix_det_pos scores))

/-- The weighted adjoint of causal softmax has reverse, upper-triangular support. -/
theorem causalSoftmax_weightedAdjoint_forbidden_entry_zero {n : ℕ}
    (π : Fin n → ℝ) (scores : Fin n → Fin n → ℝ) :
    ∀ i j, j < i →
      InfoGeometry.Probability.weightedAdjoint π (causalSoftmaxMatrix scores) i j = 0 := by
  apply InfoGeometry.Probability.weightedAdjoint_lowerTriangular_entry_zero
  intro i j hij
  change causalSoftmaxKernel scores i j = 0
  exact causalSoftmaxKernel_eq_zero_of_forbidden scores i j hij

end

theorem exists_softmaxAttention_laplacian_groupInverse [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (scores : ι → ι → ℝ) :
    ∃ D : Module.End ℝ (ι → ℝ),
      InfoGeometry.Canonical.HartwigSouriauFrameDrazin.IsGroupInverse
        (Matrix.toLin' (1 - softmaxAttentionMatrix scores)) D := by
  exact InfoGeometry.QuantumContext.MarkovDrazin.exists_stochastic_laplacian_groupInverse
    (softmaxAttentionMatrix scores) (softmaxAttentionMatrix_mem_rowStochastic scores)

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


theorem causalSoftmaxMatrix_forbidden_entry_zero {n : ℕ}
    (scores : Fin n → Fin n → ℝ) (i j : Fin n) (hij : i < j) :
    causalSoftmaxMatrix scores i j = 0 :=
  causalSoftmaxKernel_eq_zero_of_forbidden scores i j hij

end InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel
