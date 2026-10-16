/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.PolarizedAttentionReturnTrajectoryGreen

/-!
# Finite return-trajectory Kemeny trace identity for polarized attention

This module connects the finite-horizon first-return trajectory order
suprema to the algebraic return-adjusted group-inverse trace identity. The
result is a finite sum of finite-horizon suprema; it makes no infinite-path
expectation claim.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovDrazin.PolarizedAttention

open InfoGeometry.Canonical.Attention
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin
open InfoGeometry.QuantumContext.FiniteMarkovReturnTrajectoryGreen
open InfoGeometry.QuantumContext.FiniteMarkovTrajectorySuccessorLaw
open InfoGeometry.QuantumContext.MarkovDrazin
open InfoGeometry.QuantumContext.MarkovDrazin.Attention
open scoped BigOperators

variable {E V : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [AddCommMonoid V] [Module ℝ V]
variable {n : ℕ} [Fact (0 < n)]

local instance returnKemenyFinNonempty : Nonempty (Fin n) :=
  ⟨⟨0, Fact.out⟩⟩

/-- For actual polarized Gibbs-row attention, the stationary-weighted sum
over targets of the finite first-passage-after-step trajectory suprema is
`trace G + 1`, for a positive normalized stationary row weight and a group
inverse `G` of the attention Laplacian. Each supremum is over finite-horizon
trajectory integrals, including the first-return convention when `start = target`.
This is not stated as an infinite-path expected return time. -/
theorem exists_polarizedAttention_returnTrajectoryKemenyTrace
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ)
    (start : Fin n) :
    ∃ π : Fin n → ℝ, ∃ G : Matrix (Fin n) (Fin n) ℝ,
      (∀ j, 0 < π j) ∧
      (∑ j, π j = 1) ∧
      (∀ j, ∑ i, π i *
        polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β i j = π j) ∧
      IsGroupInverse
        (1 - polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β) G ∧
      ∑ target ∈ Finset.univ, π target *
        sSup (Set.range (fun horizon =>
          ∫ path, pathFirstPassageAfterStepCost target horizon start path ∂
            finiteTrajectorySuccessorLaw
              (polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β)
              (polarizedPlusAttentionMatrix_mem_rowStochastic
                (E := E) (V := V) queries ctx β)
              horizon start)) = Matrix.trace G + 1 := by
  obtain ⟨π, hπ, _hπunique⟩ :=
    existsUnique_positive_normalized_stationary_row
      (E := E) (V := V) queries ctx β
  rcases hπ with ⟨hπpos, hπsum, hπstat⟩
  obtain ⟨G, hG⟩ :=
    exists_polarizedAttention_matrix_groupInverse
      (E := E) (V := V) queries ctx β
  refine ⟨π, G, hπpos, hπsum, hπstat, hG, ?_⟩
  have hreturn (target : Fin n) :
      sSup (Set.range (fun horizon =>
        ∫ path, pathFirstPassageAfterStepCost target horizon start path ∂
          finiteTrajectorySuccessorLaw
            (polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β)
            (polarizedPlusAttentionMatrix_mem_rowStochastic
              (E := E) (V := V) queries ctx β)
            horizon start)) =
        groupInverseReturnAdjustedPotential π G start target := by
    exact trajectoryLaw_afterStepCost_sup_eq_groupInverseReturnAdjustedPotential
      (polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β) G π
      (polarizedPlusAttentionMatrix_mem_rowStochastic
        (E := E) (V := V) queries ctx β)
      (polarizedPlusAttentionMatrix_pos (E := E) (V := V) queries ctx β)
      (fun j => le_of_lt (hπpos j)) hπsum hπstat hG target start
  calc
    (∑ target ∈ Finset.univ, π target *
        sSup (Set.range (fun horizon =>
          ∫ path, pathFirstPassageAfterStepCost target horizon start path ∂
            finiteTrajectorySuccessorLaw
              (polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β)
              (polarizedPlusAttentionMatrix_mem_rowStochastic
                (E := E) (V := V) queries ctx β)
              horizon start))) =
        ∑ target ∈ Finset.univ,
          π target * groupInverseReturnAdjustedPotential π G start target := by
            apply Finset.sum_congr rfl
            intro target _
            rw [hreturn target]
    _ = Matrix.trace G + 1 :=
      weightedGroupInverseReturnAdjustedPotentialSum_eq_trace_add_one π G
        (fun j => (hπpos j).ne')
        (groupInverse_matrix_row_sum_eq_zero
          (polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β)
          G
          (polarizedPlusAttentionMatrix_mem_rowStochastic
            (E := E) (V := V) queries ctx β)
          hG)
        start

end InfoGeometry.QuantumContext.MarkovDrazin.PolarizedAttention

end noncomputable section
