/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Routing.AttentionPolytope

/-! Exact specialization to the existing finite-softmax owner.

A full-route score is the sum of the row scores selected by that route.
Its Gibbs distribution equals the independent product of the row Gibbs
weights. This is an equality of the existing operators, not a new attention
implementation or a claim of independence between actual learned tokens.
-/

namespace InfoGeometry.Routing.AttentionPolytope

open DeterministicArgmaxAttention
open scoped BigOperators

noncomputable section

variable {n m : ℕ}

/-- Additive score of a complete deterministic token-to-key route. -/
def routeScore (scores : Matrix (Fin n) (Fin m) ℝ) (f : Fin n → Fin m) : ℝ :=
  ∑ i, scores i (f i)

/-- The partition function over complete routes factors into row partitions. -/
theorem route_partition_factorization
    (scores : Matrix (Fin n) (Fin m) ℝ) (τ : ℝ) :
    FiniteSoftmax.partitionZ (routeScore scores) τ =
      ∏ i, FiniteSoftmax.partitionZ (scores i) τ := by
  unfold FiniteSoftmax.partitionZ routeScore
  simp_rw [Finset.sum_div, Real.exp_sum]
  exact (Fintype.prod_sum (fun i j => Real.exp (scores i j / τ))).symm

/-- Canonical route coordinates are exactly a softmax over additive route scores. -/
theorem routeWeight_softmax_eq
    (scores : Matrix (Fin n) (Fin m) ℝ) (τ : ℝ) (f : Fin n → Fin m) :
    routeWeight (fun i j => FiniteSoftmax.weight (scores i) τ j) f =
      FiniteSoftmax.weight (routeScore scores) τ f := by
  unfold routeWeight FiniteSoftmax.weight
  rw [Finset.prod_div_distrib, route_partition_factorization]
  congr 1
  simp [routeScore, Finset.sum_div, Real.exp_sum]

/-- Ordinary row-softmax belongs to the deterministic-route convex hull. -/
theorem softmax_mem_route_convexHull [NeZero m]
    (scores : Matrix (Fin n) (Fin m) ℝ) (τ : ℝ) :
    (fun i j => FiniteSoftmax.weight (scores i) τ j) ∈
      convexHull ℝ (Set.range (deterministicAttention (N := n) (M := m))) := by
  rw [convexHull_deterministic_eq]
  exact ⟨fun i j => (FiniteSoftmax.weight_pos (scores i) τ j).le,
    fun i => FiniteSoftmax.weight_sum_one (scores i) τ⟩

/-- Exact token readout in full-route Gibbs coordinates. -/
theorem softmax_token_readout [NeZero m]
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (scores : Matrix (Fin n) (Fin m) ℝ) (τ : ℝ) (V : Fin m → E) (i : Fin n) :
    (∑ j, FiniteSoftmax.weight (scores i) τ j • V j) =
      ∑ f : Fin n → Fin m,
        FiniteSoftmax.weight (routeScore scores) τ f • V (f i) := by
  have h := token_readout_decomposition
    (fun r j => FiniteSoftmax.weight (scores r) τ j)
    (fun r => FiniteSoftmax.weight_sum_one (scores r) τ) V i
  simpa only [routeWeight_softmax_eq] using h

end
end InfoGeometry.Routing.AttentionPolytope
