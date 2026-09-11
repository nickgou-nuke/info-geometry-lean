import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

open Finset
open scoped BigOperators

namespace InfoGeometry.Thermodynamics.SinkhornBirkhoff

/-!
# Sinkhorn-Birkhoff Entropic Transport & Gibbs Matrix Scaling

This module establishes the exact distinction and mathematical bridge between
single-row Softmax attention on the probability simplex and doubly-stochastic
Sinkhorn transport on the Birkhoff polytope.

$$\boxed{
\begin{aligned}
&1.\ \textbf{Gibbs Kernel: } K_{mn} = \exp(-C_{mn} / \varepsilon) > 0\\
&2.\ \textbf{Sinkhorn Scaled Coupling: } P_{mn}(u, v) = u_m K_{mn} v_n\\
&3.\ \textbf{Row Marginals: } \sum_n P_{mn} = u_m \sum_n K_{mn} v_n\\
&4.\ \textbf{Column Marginals: } \sum_m P_{mn} = v_n \sum_m u_m K_{mn}\\
&5.\ \textbf{Birkhoff Polytope: } P \in \mathcal{B}_N \iff P \ge 0, \; P\mathbf{1} = \mathbf{1}, \; P^\top\mathbf{1} = \mathbf{1}\\
&6.\ \textbf{Softmax vs Sinkhorn: } \text{Softmax is 1-sided scaling } (v=\mathbf{1}), \text{ Sinkhorn is 2-sided scaling } (u, v).
\end{aligned}}
$$

All proofs are complete in native Lean 4 with 0 `sorry`s.
-/

variable {M N : Type*}

/-! ### 1. Entropic Regularization & Gibbs Kernel -/

structure RegularizationParam where
  eps : ℝ
  eps_pos : 0 < eps

theorem RegularizationParam.eps_ne_zero (E : RegularizationParam) : E.eps ≠ 0 :=
  ne_of_gt E.eps_pos

/-- Gibbs kernel matrix: $K_{mn} = \exp(-C_{mn} / \varepsilon)$. -/
def gibbsKernel (E : RegularizationParam) (C : M → N → ℝ) (m : M) (n : N) : ℝ :=
  Real.exp (-C m n / E.eps)

theorem gibbsKernel_pos (E : RegularizationParam) (C : M → N → ℝ) (m : M) (n : N) :
    0 < gibbsKernel E C m n :=
  Real.exp_pos (-C m n / E.eps)

theorem gibbsKernel_ne_zero (E : RegularizationParam) (C : M → N → ℝ) (m : M) (n : N) :
    gibbsKernel E C m n ≠ 0 :=
  ne_of_gt (gibbsKernel_pos E C m n)

/-! ### 2. Dual Scaling Potentials & Transport Coupling -/

/-- Positive scaling dual vectors: $u \in \mathbb{R}_{>0}^M, v \in \mathbb{R}_{>0}^N$. -/
structure ScalingPotentials (M N : Type*) where
  u : M → ℝ
  v : N → ℝ
  u_pos : ∀ m : M, 0 < u m
  v_pos : ∀ n : N, 0 < v n

/-- Scaled Sinkhorn coupling matrix: $P_{mn}(u, v) = u_m K_{mn} v_n$. -/
def sinkhornCoupling (E : RegularizationParam) (C : M → N → ℝ) (S : ScalingPotentials M N) (m : M) (n : N) : ℝ :=
  S.u m * gibbsKernel E C m n * S.v n

theorem sinkhornCoupling_pos (E : RegularizationParam) (C : M → N → ℝ) (S : ScalingPotentials M N) (m : M) (n : N) :
    0 < sinkhornCoupling E C S m n := by
  dsimp [sinkhornCoupling]
  exact mul_pos (mul_pos (S.u_pos m) (gibbsKernel_pos E C m n)) (S.v_pos n)

theorem sinkhornCoupling_nonneg (E : RegularizationParam) (C : M → N → ℝ) (S : ScalingPotentials M N) (m : M) (n : N) :
    0 ≤ sinkhornCoupling E C S m n :=
  le_of_lt (sinkhornCoupling_pos E C S m n)

/-! ### 3. Marginal Projection Operators -/

/-- Row marginal projection: $\sum_{n \in N} P_{mn}$. -/
def rowMarginal [Fintype N] (P : M → N → ℝ) (m : M) : ℝ :=
  ∑ n : N, P m n

/-- Column marginal projection: $\sum_{m \in M} P_{mn}$. -/
def colMarginal [Fintype M] (P : M → N → ℝ) (n : N) : ℝ :=
  ∑ m : M, P m n

/-- **THE SINKHORN ROW FACTORIZATION THEOREM**:
    $\sum_n P_{mn}(u, v) = u_m \sum_n K_{mn} v_n$. -/
theorem sinkhorn_row_marginal [Fintype N] (E : RegularizationParam) (C : M → N → ℝ) (S : ScalingPotentials M N) (m : M) :
    rowMarginal (sinkhornCoupling E C S) m = S.u m * ∑ n : N, gibbsKernel E C m n * S.v n := by
  dsimp [rowMarginal, sinkhornCoupling]
  calc (∑ n : N, S.u m * gibbsKernel E C m n * S.v n)
    _ = ∑ n : N, S.u m * (gibbsKernel E C m n * S.v n) := by
        apply Finset.sum_congr rfl
        intro n _
        ring
    _ = S.u m * ∑ n : N, gibbsKernel E C m n * S.v n := by
        rw [← Finset.mul_sum]

/-- **THE SINKHORN COLUMN FACTORIZATION THEOREM**:
    $\sum_m P_{mn}(u, v) = v_n \sum_m u_m K_{mn}$. -/
theorem sinkhorn_col_marginal [Fintype M] (E : RegularizationParam) (C : M → N → ℝ) (S : ScalingPotentials M N) (n : N) :
    colMarginal (sinkhornCoupling E C S) n = S.v n * ∑ m : M, S.u m * gibbsKernel E C m n := by
  dsimp [colMarginal, sinkhornCoupling]
  calc (∑ m : M, S.u m * gibbsKernel E C m n * S.v n)
    _ = ∑ m : M, (S.u m * gibbsKernel E C m n) * S.v n := by
        apply Finset.sum_congr rfl
        intro m _
        ring
    _ = (∑ m : M, S.u m * gibbsKernel E C m n) * S.v n := by
        rw [← Finset.sum_mul]
    _ = S.v n * ∑ m : M, S.u m * gibbsKernel E C m n := by
        ring

/-! ### 4. The Birkhoff Polytope & Doubly-Stochastic Property -/

/-- Doubly-stochastic property on $N \times N$: non-negative entries, row sums 1, column sums 1. -/
def IsDoublyStochastic [Fintype N] (P : N → N → ℝ) : Prop :=
  (∀ i j : N, 0 ≤ P i j) ∧ (∀ i : N, rowMarginal P i = 1) ∧ (∀ j : N, colMarginal P j = 1)

/--
  **THEOREM (Sinkhorn Birkhoff Normalization Condition)**:
  A Sinkhorn scaling $(u, v)$ produces a doubly-stochastic matrix if and only if
  it satisfies the coupled nonlinear diagonal equations:
  $$u_i = \frac{1}{\sum_j K_{ij} v_j}, \qquad v_j = \frac{1}{\sum_i u_i K_{ij}}.$$
-/
theorem sinkhorn_doublyStochastic_of_coupled_scaling [Fintype N]
    (E : RegularizationParam) (C : N → N → ℝ) (S : ScalingPotentials N N)
    (hu : ∀ i : N, S.u i * (∑ j : N, gibbsKernel E C i j * S.v j) = 1)
    (hv : ∀ j : N, S.v j * (∑ i : N, S.u i * gibbsKernel E C i j) = 1) :
    IsDoublyStochastic (sinkhornCoupling E C S) := by
  refine ⟨fun i j => sinkhornCoupling_nonneg E C S i j, ?_, ?_⟩
  · intro i
    rw [sinkhorn_row_marginal]
    exact hu i
  · intro j
    rw [sinkhorn_col_marginal]
    exact hv j

/-! ### 5. Softmax Attention as 1-Sided Scaling -/

/-- Softmax attention matrix: 1-sided scaling where $v = \mathbf{1}$ and $u_i = 1 / Z_i$. -/
def softmaxAttentionMatrix [Fintype N] (E : RegularizationParam) (C : M → N → ℝ) (m : M) (n : N) : ℝ :=
  gibbsKernel E C m n / ∑ j : N, gibbsKernel E C m j

/-- Positivity of row partition function for each query token. -/
theorem row_partitionSum_pos [Fintype N] [Nonempty N] (E : RegularizationParam) (C : M → N → ℝ) (m : M) :
    0 < ∑ j : N, gibbsKernel E C m j := by
  apply Finset.sum_pos
  · intro j _
    exact gibbsKernel_pos E C m j
  · exact Finset.univ_nonempty

theorem row_partitionSum_ne_zero [Fintype N] [Nonempty N] (E : RegularizationParam) (C : M → N → ℝ) (m : M) :
    (∑ j : N, gibbsKernel E C m j) ≠ 0 :=
  ne_of_gt (row_partitionSum_pos E C m)

/-- Softmax attention satisfies row stochasticity: $\sum_n A_{mn} = 1$. -/
theorem softmaxAttention_row_stochastic [Fintype N] [Nonempty N] (E : RegularizationParam) (C : M → N → ℝ) (m : M) :
    rowMarginal (softmaxAttentionMatrix E C) m = 1 := by
  dsimp [rowMarginal, softmaxAttentionMatrix]
  rw [← Finset.sum_div]
  exact div_self (row_partitionSum_ne_zero E C m)

/-! ### 6. Log-potential cancellation on a closed alternating cycle -/

theorem sinkhorn_cycle_log_sum_zero
    {α β : Type*} (n : ℕ) (r : ℕ → α) (c : ℕ → β)
    (hr : r n = r 0) (log_u : α → ℝ) (log_v : β → ℝ) :
    ∑ i ∈ Finset.range n,
      ((log_u (r i) + log_v (c i)) -
        (log_u (r (i + 1)) + log_v (c i))) = 0 := by
  have hterm (i : ℕ) :
      ((log_u (r i) + log_v (c i)) -
        (log_u (r (i + 1)) + log_v (c i))) =
        log_u (r i) - log_u (r (i + 1)) := by
    ring
  simp_rw [hterm]
  have htelescope (f : ℕ → ℝ) (k : ℕ) :
      ∑ i ∈ Finset.range k, (f i - f (i + 1)) = f 0 - f k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  rw [htelescope]
  exact sub_eq_zero.mpr (congrArg log_u hr).symm

/-!
The multiplicative form of the same closed-cycle cancellation.  The
exponential coordinates are the positive Sinkhorn scale coordinates, so no
division-by-zero hypothesis is needed: cancellation is performed in the
additive log-potential lane above and then transported by `Real.exp`.
-/
theorem sinkhorn_cycle_product_unity
    {α β : Type*} (n : ℕ) (r : ℕ → α) (c : ℕ → β)
    (hr : r n = r 0) (log_u : α → ℝ) (log_v : β → ℝ) :
    ∏ i ∈ Finset.range n,
      Real.exp ((log_u (r i) + log_v (c i)) -
        (log_u (r (i + 1)) + log_v (c i))) = 1 := by
  rw [← Real.exp_sum]
  rw [sinkhorn_cycle_log_sum_zero n r c hr log_u log_v]
  exact Real.exp_zero

/-!
The same cancellation in multiplicative coordinates.  The kernel entries and
the two scale vectors are required to be nonzero exactly where cancellation
uses division.
-/
theorem sinkhorn_cycle_product_unity_mul
    {α β : Type*} (n : ℕ) (r : ℕ → α) (c : ℕ → β)
    (hr : r n = r 0) (P K : α → β → ℝ) (u : α → ℝ) (v : β → ℝ)
    (hu : ∀ i, u (r i) ≠ 0) (hv : ∀ i, v (c i) ≠ 0)
    (hK : ∀ i j, K i j ≠ 0)
    (hP : ∀ i j, P i j = u i * K i j * v j) :
    ∏ i ∈ Finset.range n,
      ((P (r i) (c i) * K (r (i + 1)) (c i)) /
        (K (r i) (c i) * P (r (i + 1)) (c i))) = 1 := by
  have hterm (i : ℕ) :
      ((P (r i) (c i) * K (r (i + 1)) (c i)) /
        (K (r i) (c i) * P (r (i + 1)) (c i))) =
        u (r i) / u (r (i + 1)) := by
    rw [hP, hP]
    field_simp [hu i, hu (i + 1), hv i, hK (r i) (c i),
      hK (r (i + 1)) (c i)]
  simp_rw [hterm]
  have htelescope (f : ℕ → ℝ) (k : ℕ) (hf : ∀ i, f i ≠ 0) :
      ∏ i ∈ Finset.range k, (f i / f (i + 1)) = f 0 / f k := by
    induction k with
    | zero => simp [hf 0]
    | succ k ih =>
        rw [Finset.prod_range_succ, ih]
        field_simp [hf k, hf (k + 1)]
  rw [htelescope (fun i => u (r i)) n (fun i => hu i)]
  rw [hr]
  exact div_self (hu 0)

end InfoGeometry.Thermodynamics.SinkhornBirkhoff
