/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import InfoGeometry.Epistemology.VariationalRG

/-!
# Finite Fisher Metric Identities for Congruent Markov Kernels

This module formalizes the core differential-geometric invariance theorem of Chentsov:
1. `ProbInterior`: Probability distributions on finite types strictly residing in the
   simplex interior ($P(a) > 0$ and $\sum_a P(a) = 1$), with constructive witness `unitProbInterior`.
2. `TangentVector`: Tangent vectors to the probability simplex ($\sum_a v(a) = 0$),
   with constructive witness `zeroTangentVector`.
3. `fisherMetric`: The Riemannian metric tensor $g_P(u, v) = \sum_a \frac{u(a) v(a)}{P(a)}$
   on the simplex interior, together with symmetry, non-negativity, strict positive-definiteness
   (`fisherMetric_eq_zero_iff`, `fisherMetric_pos_of_ne_zero`), score representation,
   and scalar homogeneity (`fisherMetric_zero_left`, `fisherMetric_zero_right`,
   `fisherMetric_smul_left`, `fisherMetric_smul_right`).
4. `pushforwardTangent`: Action of a Markov transition kernel on simplex tangent vectors,
   preserving the zero-sum tangent condition $\sum_b (T_* v)(b) = 0$.
5. `CongruentMarkovKernel`: A Markov kernel $T : \alpha \to \beta$ with disjoint fiber supports
   (each output state $b \in \beta$ is reachable from at most one input state $a \in \alpha$),
   with constructive identity witness `idCongruentMarkovKernel` and `pushforwardTangentVec_id`.
6. `chentsov_congruent_metric_invariance` & `chentsov_congruent_pushforward_fisher_isometry`:
   Exact invariance of the finite Fisher sum under the stated congruent-kernel hypotheses:
   $$g_{T_* P}(T_* u, T_* v) = g_P(u, v)$$
7. `CongruentPartitionEmbedding` & `chentsov_partition_embedding_fisher_invariance`:
   Sufficient statistic partition embeddings $\pi : \beta \to \alpha$ with positive fiber weights
   $c_b > 0$ summing to $1$ on each fiber $\pi^{-1}(a)$ induce full-support congruent Markov
   kernels preserving the Fisher metric.
8. `injectiveCongruentKernel` & `injectiveCongruentKernel_supportMaskedFisher_sum`:
   Injective sample-space embeddings induce a support-masked finite sum identity. When the
   embedding is not surjective, the pushed distribution is on the boundary of the target
   simplex, so this theorem is not an interior Fisher isometry.
-/

namespace InfoGeometry.Epistemology.ChentsovMetricInvariance

open Finset
open scoped BigOperators
open InfoGeometry.Epistemology.VariationalRG

/-! ### 1. Simplex Interior and Tangent Vectors -/

/-- A probability distribution strictly in the interior of the simplex. -/
structure ProbInterior (α : Type*) [Fintype α] where
  p : α → ℝ
  pos : ∀ a, 0 < p a
  sum_one : ∑ a, p a = 1

/-- Canonical interior probability distribution on the one-point space `Unit`. -/
noncomputable def unitProbInterior : ProbInterior Unit where
  p := fun _ => 1
  pos := fun _ => zero_lt_one
  sum_one := by simp

noncomputable instance : Inhabited (ProbInterior Unit) :=
  ⟨unitProbInterior⟩

/-- Coercion from an interior distribution to a general probability distribution. -/
noncomputable def toProbDist {α : Type*} [Fintype α] (P : ProbInterior α) : ProbDist α where
  p := P.p
  nonneg a := le_of_lt (P.pos a)
  sum_one := P.sum_one

/-- A tangent vector to the probability simplex (infinitesimal probability perturbation). -/
structure TangentVector (α : Type*) [Fintype α] where
  v : α → ℝ
  sum_zero : ∑ a, v a = 0

/-- Zero tangent vector on the probability simplex over `α`. -/
def zeroTangentVector (α : Type*) [Fintype α] : TangentVector α where
  v := fun _ => 0
  sum_zero := by simp

/-- Closed concrete witness for `TangentVector` on `Unit`. -/
def unitTangentVector : TangentVector Unit :=
  zeroTangentVector Unit

instance {α : Type*} [Fintype α] : Inhabited (TangentVector α) :=
  ⟨zeroTangentVector α⟩

/-! ### 2. The Fisher Information Metric -/

/-- The Fisher information metric tensor on the simplex interior:
    `g_P(u, v) = ∑_a (u(a) * v(a)) / P(a)`. -/
noncomputable def fisherMetric {α : Type*} [Fintype α]
    (P : ProbInterior α) (u v : α → ℝ) : ℝ :=
  ∑ a, (u a * v a) / P.p a

/-- Symmetry of the Fisher metric tensor: `g_P(u, v) = g_P(v, u)`. -/
theorem fisherMetric_symm {α : Type*} [Fintype α]
    (P : ProbInterior α) (u v : α → ℝ) :
    fisherMetric P u v = fisherMetric P v u := by
  unfold fisherMetric
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_comm]

/-- Non-negativity of the Fisher metric quadratic form: `0 ≤ g_P(u, u)`. -/
theorem fisherMetric_nonneg {α : Type*} [Fintype α]
    (P : ProbInterior α) (u : α → ℝ) :
    0 ≤ fisherMetric P u u := by
  unfold fisherMetric
  apply Finset.sum_nonneg
  intro a _
  have h_num : 0 ≤ u a * u a := mul_self_nonneg (u a)
  have h_den : 0 ≤ P.p a := le_of_lt (P.pos a)
  exact div_nonneg h_num h_den

/-- The Fisher metric vanishes when the left tangent argument is zero. -/
@[simp]
theorem fisherMetric_zero_left {α : Type*} [Fintype α]
    (P : ProbInterior α) (v : α → ℝ) :
    fisherMetric P (fun _ => 0) v = 0 := by
  unfold fisherMetric
  simp

/-- The Fisher metric vanishes when the right tangent argument is zero. -/
@[simp]
theorem fisherMetric_zero_right {α : Type*} [Fintype α]
    (P : ProbInterior α) (u : α → ℝ) :
    fisherMetric P u (fun _ => 0) = 0 := by
  unfold fisherMetric
  simp

/-- Strict positive-definiteness of the Fisher metric on the simplex interior:
`g_P(u, u) = 0 ↔ u = 0`. -/
theorem fisherMetric_eq_zero_iff {α : Type*} [Fintype α]
    (P : ProbInterior α) (u : α → ℝ) :
    fisherMetric P u u = 0 ↔ u = 0 := by
  constructor
  · intro h_zero
    unfold fisherMetric at h_zero
    have h_nonneg : ∀ a ∈ (Finset.univ : Finset α), 0 ≤ (u a * u a) / P.p a := by
      intro a _
      exact div_nonneg (mul_self_nonneg (u a)) (le_of_lt (P.pos a))
    have h_terms := (Finset.sum_eq_zero_iff_of_nonneg h_nonneg).mp h_zero
    funext a
    have ha := h_terms a (Finset.mem_univ a)
    have h_p_ne : P.p a ≠ 0 := ne_of_gt (P.pos a)
    have h_mul : u a * u a = 0 := by
      rcases div_eq_zero_iff.mp ha with h_num | h_den
      · exact h_num
      · exact False.elim (h_p_ne h_den)
    exact mul_self_eq_zero.mp h_mul
  · rintro rfl
    unfold fisherMetric
    simp

/-- Strict positivity of the Fisher metric quadratic form on nonzero tangent vectors:
`u ≠ 0 → 0 < g_P(u, u)`. -/
theorem fisherMetric_pos_of_ne_zero {α : Type*} [Fintype α]
    (P : ProbInterior α) (u : α → ℝ) (hu : u ≠ 0) :
    0 < fisherMetric P u u := by
  refine lt_of_le_of_ne (fisherMetric_nonneg P u) ?_
  intro h_eq
  exact hu ((fisherMetric_eq_zero_iff P u).mp h_eq.symm)

/-- Left scalar homogeneity of the Fisher metric tensor. -/
theorem fisherMetric_smul_left {α : Type*} [Fintype α]
    (P : ProbInterior α) (c : ℝ) (u v : α → ℝ) :
    fisherMetric P (fun a => c * u a) v = c * fisherMetric P u v := by
  unfold fisherMetric
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Right scalar homogeneity of the Fisher metric tensor. -/
theorem fisherMetric_smul_right {α : Type*} [Fintype α]
    (P : ProbInterior α) (c : ℝ) (u v : α → ℝ) :
    fisherMetric P u (fun a => c * v a) = c * fisherMetric P u v := by
  unfold fisherMetric
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Score representation of the Fisher metric:
    `g_P(u, v) = ∑_a P(a) * (u(a)/P(a)) * (v(a)/P(a))`. -/
theorem fisherMetric_eq_score_expectation {α : Type*} [Fintype α]
    (P : ProbInterior α) (u v : α → ℝ) :
    fisherMetric P u v = ∑ a, P.p a * ((u a / P.p a) * (v a / P.p a)) := by
  unfold fisherMetric
  apply Finset.sum_congr rfl
  intro a _
  have hpos : P.p a ≠ 0 := ne_of_gt (P.pos a)
  field_simp [hpos]

/-! ### 3. Markov Pushforward of Tangent Vectors -/

/-- Pushforward of a tangent vector under a Markov transition kernel:
    `(T_* u)(b) = ∑_a u(a) * T(a, b)`. -/
def pushforwardTangentVec {α β : Type*} [Fintype α] [Fintype β]
    (T : MarkovKernel α β) (u : α → ℝ) : β → ℝ :=
  fun b => ∑ a, u a * T.T a b

/-- Theorem: Markov pushforward preserves the zero-sum tangent condition:
    `∑_b (T_* u)(b) = 0` whenever `∑_a u(a) = 0`. -/
theorem pushforwardTangent_sum_zero {α β : Type*} [Fintype α] [Fintype β]
    (T : MarkovKernel α β) (u : TangentVector α) :
    ∑ b, pushforwardTangentVec T u.v b = 0 := by
  calc
    ∑ b, pushforwardTangentVec T u.v b
      = ∑ b, ∑ a, u.v a * T.T a b := rfl
    _ = ∑ a, ∑ b, u.v a * T.T a b := Finset.sum_comm
    _ = ∑ a, u.v a * ∑ b, T.T a b := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.mul_sum]
    _ = ∑ a, u.v a * 1 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [T.sum_one a]
    _ = ∑ a, u.v a := by simp only [mul_one]
    _ = 0 := u.sum_zero

/-- The packaged pushforward of a tangent vector as a `TangentVector β`. -/
def pushforwardTangent {α β : Type*} [Fintype α] [Fintype β]
    (T : MarkovKernel α β) (u : TangentVector α) : TangentVector β where
  v := pushforwardTangentVec T u.v
  sum_zero := pushforwardTangent_sum_zero T u

/-! ### 4. Congruent Markov Embeddings -/

/--
  A congruent Markov kernel is a Markov transition kernel with partitioned/disjoint fibers:
  each output state `b : β` receives probability mass from at most one input state `fiber b`.
  That is, if `T.T a b ≠ 0`, then `a = fiber b`.
-/
structure CongruentMarkovKernel (α β : Type*) [Fintype α] [Fintype β] where
  kernel : MarkovKernel α β
  fiber : β → α
  fiber_prop : ∀ a b, kernel.T a b ≠ 0 → fiber b = a

/-- Identity congruent Markov kernel on a finite type `α`. -/
def idCongruentMarkovKernel (α : Type*) [Fintype α] [DecidableEq α] :
    CongruentMarkovKernel α α where
  kernel := {
    T a b := if b = a then 1 else 0
    nonneg a b := by
      split_ifs <;> linarith
    sum_one a := by
      have : ∑ b, (if b = a then (1 : ℝ) else 0) = 1 := by
        rw [Finset.sum_ite_eq']
        simp
      exact this
  }
  fiber := id
  fiber_prop a b := by
    dsimp
    split_ifs with h_eq
    · intro _
      exact h_eq
    · intro h_abs
      contradiction

instance {α : Type*} [Fintype α] [DecidableEq α] :
    Inhabited (CongruentMarkovKernel α α) :=
  ⟨idCongruentMarkovKernel α⟩

/-- Closed concrete witness for `CongruentMarkovKernel` on `Unit`. -/
def unitCongruentMarkovKernel : CongruentMarkovKernel Unit Unit :=
  idCongruentMarkovKernel Unit

/-- For a congruent kernel, `T(a, b) = 0` whenever `a ≠ fiber b`. -/
theorem congruent_kernel_zero_of_ne {α β : Type*} [Fintype α] [Fintype β]
    (CK : CongruentMarkovKernel α β) (a : α) (b : β) (h : a ≠ CK.fiber b) :
    CK.kernel.T a b = 0 := by
  by_contra hne
  have heq := CK.fiber_prop a b hne
  exact h (heq.symm)

/--
  Pushforward of an interior distribution under a congruent kernel collapses to a single fiber term:
  `(T_* P)(b) = P(fiber b) * T(fiber b, b)`.
-/
theorem congruent_pushforward_at {α β : Type*} [Fintype α] [Fintype β]
    (CK : CongruentMarkovKernel α β) (P : ProbInterior α) (b : β) :
    (pushforward CK.kernel (toProbDist P)).p b = P.p (CK.fiber b) * CK.kernel.T (CK.fiber b) b := by
  dsimp [pushforward, toProbDist]
  rw [← Finset.sum_subset (Finset.subset_univ {CK.fiber b})]
  · simp only [Finset.sum_singleton]
  · intro a _ hnot_in
    have h_ne : a ≠ CK.fiber b := by
      intro h_eq
      apply hnot_in
      simp only [Finset.mem_singleton, h_eq]
    rw [congruent_kernel_zero_of_ne CK a b h_ne, mul_zero]

/--
  Pushforward of a tangent vector under a congruent kernel collapses to a single fiber term:
  `(T_* u)(b) = u(fiber b) * T(fiber b, b)`.
-/
theorem congruent_pushforward_tangent_at {α β : Type*} [Fintype α] [Fintype β]
    (CK : CongruentMarkovKernel α β) (u : α → ℝ) (b : β) :
    pushforwardTangentVec CK.kernel u b = u (CK.fiber b) * CK.kernel.T (CK.fiber b) b := by
  dsimp [pushforwardTangentVec]
  rw [← Finset.sum_subset (Finset.subset_univ {CK.fiber b})]
  · simp only [Finset.sum_singleton]
  · intro a _ hnot_in
    have h_ne : a ≠ CK.fiber b := by
      intro h_eq
      apply hnot_in
      simp only [Finset.mem_singleton, h_eq]
    rw [congruent_kernel_zero_of_ne CK a b h_ne, mul_zero]

/-- Pushing a tangent vector forward along the identity congruent Markov kernel is the identity. -/
@[simp]
theorem pushforwardTangentVec_id {α : Type*} [Fintype α] [DecidableEq α]
    (u : α → ℝ) :
    pushforwardTangentVec (idCongruentMarkovKernel α).kernel u = u := by
  funext b
  rw [congruent_pushforward_tangent_at (idCongruentMarkovKernel α) u b]
  dsimp [idCongruentMarkovKernel]
  simp

/-! ### 5. Chentsov's Invariance Theorem -/

/--
  **Chentsov's Congruent Metric Invariance Theorem**:
  Under any congruent Markov embedding `T : α → β`, the pull-back of the Fisher
  information metric tensor on the image equals the Fisher information metric
  on the base simplex identically:
  $$\sum_{b \in \beta, T(fiber b, b) > 0} \frac{(T_* u)(b) (T_* v)(b)}{(T_* P)(b)} = g_P(u, v)$$
-/
theorem chentsov_congruent_metric_invariance {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (CK : CongruentMarkovKernel α β) (P : ProbInterior α) (u v : α → ℝ) :
    ∑ b, (if CK.kernel.T (CK.fiber b) b = 0 then 0 else
      (pushforwardTangentVec CK.kernel u b * pushforwardTangentVec CK.kernel v b) /
      (pushforward CK.kernel (toProbDist P)).p b) =
    fisherMetric P u v := by
  have h_fiber_term : ∀ b,
      (if CK.kernel.T (CK.fiber b) b = 0 then 0 else
        (pushforwardTangentVec CK.kernel u b * pushforwardTangentVec CK.kernel v b) /
        (pushforward CK.kernel (toProbDist P)).p b) =
      ((u (CK.fiber b) * v (CK.fiber b)) / P.p (CK.fiber b)) * CK.kernel.T (CK.fiber b) b := by
    intro b
    rw [congruent_pushforward_at CK P b, congruent_pushforward_tangent_at CK u b,
        congruent_pushforward_tangent_at CK v b]
    by_cases h_zero : CK.kernel.T (CK.fiber b) b = 0
    · simp [h_zero]
    · simp [h_zero]
      calc
        (u (CK.fiber b) * CK.kernel.T (CK.fiber b) b * (v (CK.fiber b) * CK.kernel.T (CK.fiber b) b)) /
        (P.p (CK.fiber b) * CK.kernel.T (CK.fiber b) b)
          = ((u (CK.fiber b) * v (CK.fiber b)) * (CK.kernel.T (CK.fiber b) b * CK.kernel.T (CK.fiber b) b)) /
            (P.p (CK.fiber b) * CK.kernel.T (CK.fiber b) b) := by ring
        _ = ((u (CK.fiber b) * v (CK.fiber b)) / P.p (CK.fiber b)) *
            ((CK.kernel.T (CK.fiber b) b * CK.kernel.T (CK.fiber b) b) / CK.kernel.T (CK.fiber b) b) := by
          rw [mul_div_mul_comm]
        _ = ((u (CK.fiber b) * v (CK.fiber b)) / P.p (CK.fiber b)) * CK.kernel.T (CK.fiber b) b := by
          rw [mul_self_div_self]

  calc
    ∑ b, (if CK.kernel.T (CK.fiber b) b = 0 then 0 else
      (pushforwardTangentVec CK.kernel u b * pushforwardTangentVec CK.kernel v b) /
      (pushforward CK.kernel (toProbDist P)).p b)
      = ∑ b, (((u (CK.fiber b) * v (CK.fiber b)) / P.p (CK.fiber b)) * CK.kernel.T (CK.fiber b) b) := by
        apply Finset.sum_congr rfl
        intro b _
        exact h_fiber_term b
    _ = ∑ a, ∑ b ∈ Finset.filter (fun b => CK.fiber b = a) Finset.univ,
          (((u (CK.fiber b) * v (CK.fiber b)) / P.p (CK.fiber b)) * CK.kernel.T (CK.fiber b) b) := by
        rw [← Finset.sum_fiberwise_of_maps_to (fun b _ => Finset.mem_univ (CK.fiber b))]
    _ = ∑ a, ∑ b ∈ Finset.filter (fun b => CK.fiber b = a) Finset.univ,
          (((u a * v a) / P.p a) * CK.kernel.T a b) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        rw [hb]
    _ = ∑ a, ((u a * v a) / P.p a) * ∑ b ∈ Finset.filter (fun b => CK.fiber b = a) Finset.univ, CK.kernel.T a b := by
        apply Finset.sum_congr rfl
        intro a _
        rw [← Finset.mul_sum]
    _ = ∑ a, ((u a * v a) / P.p a) * ∑ b, CK.kernel.T a b := by
        apply Finset.sum_congr rfl
        intro a _
        congr 1
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun b => CK.fiber b = a)]
        have h_rest_zero : ∑ b ∈ Finset.filter (fun b => ¬CK.fiber b = a) Finset.univ, CK.kernel.T a b = 0 := by
          apply Finset.sum_eq_zero
          intro b hb
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
          exact congruent_kernel_zero_of_ne CK a b (Ne.symm hb)
        rw [h_rest_zero, add_zero]
    _ = ∑ a, ((u a * v a) / P.p a) * 1 := by
        apply Finset.sum_congr rfl
        intro a _
        rw [CK.kernel.sum_one a]
    _ = ∑ a, (u a * v a) / P.p a := by
        apply Finset.sum_congr rfl
        intro a _
        rw [mul_one]
    _ = fisherMetric P u v := rfl

/-- The pushforward of an interior distribution remains in the simplex interior
when every output has positive transition weight from its assigned fiber. -/
noncomputable def congruentPushforwardInterior {α β : Type*} [Fintype α] [Fintype β]
    (CK : CongruentMarkovKernel α β) (P : ProbInterior α)
    (h_weight : ∀ b, 0 < CK.kernel.T (CK.fiber b) b) : ProbInterior β where
  p := (pushforward CK.kernel (toProbDist P)).p
  pos b := by
    rw [congruent_pushforward_at CK P b]
    exact mul_pos (P.pos (CK.fiber b)) (h_weight b)
  sum_one := (pushforward CK.kernel (toProbDist P)).sum_one

/-- Full-support congruent Markov embeddings preserve the native Fisher metric
as an equality of simplex-interior metrics on the source and target. -/
theorem chentsov_congruent_pushforward_fisher_isometry
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (CK : CongruentMarkovKernel α β) (P : ProbInterior α)
    (h_weight : ∀ b, 0 < CK.kernel.T (CK.fiber b) b) (u v : α → ℝ) :
    fisherMetric (congruentPushforwardInterior CK P h_weight)
        (pushforwardTangentVec CK.kernel u) (pushforwardTangentVec CK.kernel v) =
      fisherMetric P u v := by
  unfold fisherMetric congruentPushforwardInterior
  change (∑ b, (pushforwardTangentVec CK.kernel u b * pushforwardTangentVec CK.kernel v b) /
      (pushforward CK.kernel (toProbDist P)).p b) = fisherMetric P u v
  have h_term (b : β) :
      (pushforwardTangentVec CK.kernel u b * pushforwardTangentVec CK.kernel v b) /
          (pushforward CK.kernel (toProbDist P)).p b =
        (if CK.kernel.T (CK.fiber b) b = 0 then 0 else
          (pushforwardTangentVec CK.kernel u b * pushforwardTangentVec CK.kernel v b) /
            (pushforward CK.kernel (toProbDist P)).p b) := by
    simp [ne_of_gt (h_weight b)]
  calc
    _ = ∑ b, (if CK.kernel.T (CK.fiber b) b = 0 then 0 else
          (pushforwardTangentVec CK.kernel u b * pushforwardTangentVec CK.kernel v b) /
            (pushforward CK.kernel (toProbDist P)).p b) := by
          apply Finset.sum_congr rfl
          intro b _
          exact h_term b
    _ = fisherMetric P u v := chentsov_congruent_metric_invariance CK P u v

/-! ### 6. Sufficient Statistic Partition Embeddings -/

/-- A sufficient statistic partition embedding `π : β → α` with strictly positive
conditional fiber weights `c : β → ℝ` summing to `1` over each fiber `π⁻¹(a)`. -/
structure CongruentPartitionEmbedding (α β : Type*) [Fintype α] [Fintype β] [DecidableEq α] where
  π : β → α
  c : β → ℝ
  c_pos : ∀ b, 0 < c b
  partition_sum : ∀ a : α, ∑ b ∈ Finset.univ.filter (fun b => π b = a), c b = 1

/-- Identity partition embedding on a finite type; each singleton fiber has weight one. -/
def idCongruentPartitionEmbedding (α : Type*) [Fintype α] [DecidableEq α] :
    CongruentPartitionEmbedding α α where
  π := id
  c := fun _ => 1
  c_pos := fun _ => zero_lt_one
  partition_sum a := by
    rw [Finset.sum_filter]
    dsimp only [id]
    rw [Finset.sum_ite_eq']
    simp

instance {α : Type*} [Fintype α] [DecidableEq α] :
    Inhabited (CongruentPartitionEmbedding α α) :=
  ⟨idCongruentPartitionEmbedding α⟩

/-- A closed nonempty model of the partition embedding structure on the singleton type. -/
def unitCongruentPartitionEmbedding : CongruentPartitionEmbedding Unit Unit :=
  idCongruentPartitionEmbedding Unit

/-- Every sufficient statistic partition embedding canonically induces a congruent Markov kernel
`T(a, b) = c(b) δ_{π(b), a}`. -/
def partitionEmbeddingToKernel {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (E : CongruentPartitionEmbedding α β) : CongruentMarkovKernel α β where
  kernel := {
    T a b := if E.π b = a then E.c b else 0
    nonneg a b := by
      split_ifs
      · exact le_of_lt (E.c_pos b)
      · exact le_refl 0
    sum_one a := by
      rw [← Finset.sum_filter]
      exact E.partition_sum a
  }
  fiber := E.π
  fiber_prop a b := by
    dsimp
    split_ifs with h_eq
    · intro _
      exact h_eq
    · intro h_abs
      contradiction

/-- Every output state `b` in a partition embedding has strictly positive transition weight
from its assigned sufficient-statistic fiber `E.π b`. -/
theorem partitionEmbedding_weight_pos {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (E : CongruentPartitionEmbedding α β) (b : β) :
    0 < (partitionEmbeddingToKernel E).kernel.T ((partitionEmbeddingToKernel E).fiber b) b := by
  dsimp [partitionEmbeddingToKernel]
  simp
  exact E.c_pos b

/-- **Chentsov's Partition Embedding Fisher Invariance Theorem**:
Every sufficient statistic partition embedding `E : CongruentPartitionEmbedding α β`
is an exact Fisher-metric isometry from `ProbInterior α` into `ProbInterior β`. -/
theorem chentsov_partition_embedding_fisher_invariance
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (E : CongruentPartitionEmbedding α β) (P : ProbInterior α) (u v : α → ℝ) :
    fisherMetric
        (congruentPushforwardInterior (partitionEmbeddingToKernel E) P
          (partitionEmbedding_weight_pos E))
        (pushforwardTangentVec (partitionEmbeddingToKernel E).kernel u)
        (pushforwardTangentVec (partitionEmbeddingToKernel E).kernel v) =
      fisherMetric P u v :=
  chentsov_congruent_pushforward_fisher_isometry
    (partitionEmbeddingToKernel E) P (partitionEmbedding_weight_pos E) u v

/-! ### 7. Canonical Injective Embeddings -/

/--
  Any injection `f : α ↪ β` with a retraction `retract : β → α` satisfying
  `retract (f a) = a` gives rise to a canonical congruent Markov kernel.
-/
def injectiveCongruentKernel {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α ↪ β) (retract : β → α) (h_retract : ∀ a, retract (f a) = a) :
    CongruentMarkovKernel α β where
  kernel := {
    T a b := if b = f a then 1 else 0
    nonneg a b := by
      split_ifs <;> linarith
    sum_one a := by
      have : ∑ b, (if b = f a then (1 : ℝ) else 0) = 1 := by
        rw [Finset.sum_ite_eq']
        simp
      exact this
  }
  fiber := retract
  fiber_prop a b := by
    dsimp
    split_ifs with h_eq
    · rw [h_eq, h_retract]
      intro _
      rfl
    · intro h_abs
      contradiction

/-- Support-masked finite sum identity for an injective sample-space embedding. For a
non-surjective embedding the pushforward has zero coordinates, so the masked sum here
is not asserted to be the Fisher metric on the target simplex interior. -/
theorem injectiveCongruentKernel_supportMaskedFisher_sum
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (f : α ↪ β) (retract : β → α) (h_retract : ∀ a, retract (f a) = a)
    (P : ProbInterior α) (u v : α → ℝ) :
    ∑ b, (if (injectiveCongruentKernel f retract h_retract).kernel.T
          ((injectiveCongruentKernel f retract h_retract).fiber b) b = 0 then 0 else
        (pushforwardTangentVec (injectiveCongruentKernel f retract h_retract).kernel u b *
          pushforwardTangentVec (injectiveCongruentKernel f retract h_retract).kernel v b) /
        (pushforward (injectiveCongruentKernel f retract h_retract).kernel (toProbDist P)).p b) =
      fisherMetric P u v :=
  chentsov_congruent_metric_invariance (injectiveCongruentKernel f retract h_retract) P u v

end InfoGeometry.Epistemology.ChentsovMetricInvariance
