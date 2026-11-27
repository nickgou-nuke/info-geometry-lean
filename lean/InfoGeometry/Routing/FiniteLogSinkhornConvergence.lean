/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Routing.FiniteLogSinkhorn
import InfoGeometry.Physics.SinkhornPositiveConvergence
import Mathlib.Analysis.Convex.DoublyStochasticMatrix

/-!
# Convergence of the existing finite log-domain iteration

The existing `sinkhornPotentials`/`sinkhornMatrix` recurrence is identified
with the alternating marginal projections whose convergence is proved in
`SinkhornPositiveConvergence`. The limit theorem concerns the actual routing
owner, including its original zero-potential initialization.
-/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace InfoGeometry.Routing.FiniteLogSinkhorn
open InfoGeometry.Physics.AmariSinkhornAlternatingProjections
variable {K : Type*} [Fintype K] [Nonempty K]

/-- Row normalization cancels the old row potential. -/
theorem rowUpdate_exp_potentials (S : Matrix K K ℝ) (u v : K → ℝ) :
    sinkhornRowUpdate (fun i j => Real.exp (S i j + u i + v j)) (fun _ => 1) =
      (fun i j => Real.exp (S i j - logsumexp (fun k => S i k + v k) + v j)) := by
  funext i j
  let Z := FiniteSoftmax.partitionZ (fun k => S i k + v k) 1
  have hZ : 0 < Z := FiniteSoftmax.partitionZ_pos _ _
  have hf (k : K) : Real.exp (S i k + u i + v k) =
      Real.exp (u i) * Real.exp (S i k + v k) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hrhs : Real.exp (S i j - logsumexp (fun k => S i k + v k) + v j) =
      Real.exp (S i j + v j) / Z := by
    have harg : S i j - logsumexp (fun k => S i k + v k) + v j =
        (S i j + v j) - logsumexp (fun k => S i k + v k) := by ring
    rw [harg, Real.exp_sub, logsumexp, Real.exp_log hZ]
  rw [hrhs]
  unfold sinkhornRowUpdate
  simp_rw [hf]
  rw [← Finset.mul_sum]
  have hsum : (∑ k, Real.exp (S i k + v k)) = Z := by
    simp [Z, FiniteSoftmax.partitionZ]
  rw [hsum]
  field_simp [(Real.exp_pos (u i)).ne', hZ.ne'] <;> ring

/-- Column normalization cancels the old column potential. -/
theorem colUpdate_exp_potentials (S : Matrix K K ℝ) (u v : K → ℝ) :
    sinkhornColUpdate (fun i j => Real.exp (S i j + u i + v j)) (fun _ => 1) =
      (fun i j => Real.exp (S i j + u i - logsumexp (fun k => S k j + u k))) := by
  funext i j
  let Z := FiniteSoftmax.partitionZ (fun k => S k j + u k) 1
  have hZ : 0 < Z := FiniteSoftmax.partitionZ_pos _ _
  have hf (k : K) : Real.exp (S k j + u k + v j) =
      Real.exp (v j) * Real.exp (S k j + u k) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hrhs : Real.exp (S i j + u i - logsumexp (fun k => S k j + u k)) =
      Real.exp (S i j + u i) / Z := by
    rw [Real.exp_sub, logsumexp, Real.exp_log hZ]
  rw [hrhs]
  unfold sinkhornColUpdate
  simp_rw [hf]
  rw [← Finset.mul_sum]
  have hsum : (∑ k, Real.exp (S k j + u k)) = Z := by
    simp [Z, FiniteSoftmax.partitionZ]
  rw [hsum]
  field_simp [(Real.exp_pos (v j)).ne', hZ.ne'] <;> ring

/-- Exact equality with the original log-potential recurrence at every step. -/
theorem sinkhornMatrix_eq_actualIterates (S : Matrix K K ℝ) (n : ℕ) :
    sinkhornMatrix n S =
      sinkhornIterates (fun i j => Real.exp (S i j)) (fun _ => 1) (fun _ => 1) n := by
  induction n with
  | zero =>
    funext i j
    simp [sinkhornMatrix, sinkhornPotentials]
  | succ n ih =>
    rw [sinkhornIterates_succ, ← ih]
    let uv := sinkhornPotentials S n
    change (fun i j => Real.exp (S i j +
        (-logsumexp (fun k => S i k + uv.2 k)) +
        (-logsumexp (fun k => S k j + (-logsumexp (fun l => S k l + uv.2 l)))))) =
      sinkhornColUpdate
        (sinkhornRowUpdate (fun i j => Real.exp (S i j + uv.1 i + uv.2 j))
          (fun _ => 1)) (fun _ => 1)
    rw [rowUpdate_exp_potentials]
    have hrow : (fun i j => Real.exp (S i j - logsumexp (fun k => S i k + uv.2 k) + uv.2 j)) =
        (fun i j => Real.exp (S i j + (-logsumexp (fun k => S i k + uv.2 k)) + uv.2 j)) := by
      simp only [sub_eq_add_neg]
    rw [hrow, colUpdate_exp_potentials]
    simp only [sub_eq_add_neg]

variable [DecidableEq K]

/-- The existing routing iteration converges to the unique doubly stochastic KL projection. -/
theorem sinkhornMatrix_converges_to_KL_projection (S : Matrix K K ℝ) :
    ∃ Q : Matrix K K ℝ,
      (∀ i j, 0 < Q i j) ∧ Q ∈ doublyStochastic ℝ K ∧
      Tendsto (fun n => sinkhornMatrix n S) atTop (𝓝 Q) ∧
      (∀ P : Matrix K K ℝ, P ∈ doublyStochastic ℝ K →
        matrixKL P (fun i j => Real.exp (S i j)) = matrixKL P Q +
          matrixKL Q (fun i j => Real.exp (S i j)) ∧
        matrixKL Q (fun i j => Real.exp (S i j)) ≤
          matrixKL P (fun i j => Real.exp (S i j)) ∧
        (matrixKL P (fun i j => Real.exp (S i j)) =
          matrixKL Q (fun i j => Real.exp (S i j)) ↔ P = Q)) := by
  obtain ⟨Q, hQ, hr, hc, ht, hmin⟩ := exists_unique_sinkhorn_KL_projection
    (fun i j => Real.exp (S i j)) (fun _ => 1) (fun _ => 1)
    (fun _ _ => Real.exp_pos _) (fun _ => zero_lt_one) (fun _ => zero_lt_one) rfl
  refine ⟨Matrix.of Q, hQ, ?_, ?_, ?_⟩
  · exact (mem_doublyStochastic_iff_sum (M := Matrix.of Q)).2
      ⟨fun i j => (hQ i j).le, hr, hc⟩
  · have hcast : Continuous (fun A : TransportPlan K K => Matrix.of A) := by
      change Continuous (fun A : TransportPlan K K => A)
      exact continuous_id
    have heq : (fun n => sinkhornMatrix n S) =
        (fun n => Matrix.of (sinkhornIterates (fun i j => Real.exp (S i j))
          (fun _ => 1) (fun _ => 1) n)) := by
      funext n
      exact sinkhornMatrix_eq_actualIterates S n
    rw [heq]
    exact hcast.continuousAt.tendsto.comp ht
  · intro P hP
    rw [mem_doublyStochastic_iff_sum] at hP
    exact hmin P hP.1 hP.2.1 hP.2.2

end InfoGeometry.Routing.FiniteLogSinkhorn
