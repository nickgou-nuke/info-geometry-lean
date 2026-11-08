/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.PolarizedAttentionReturnTrajectoryGreen
import InfoGeometry.QuantumContext.PolarizedAttentionReturnKemeny
import InfoGeometry.QuantumContext.FiniteMarkovReturnTrajectoryColimit
import InfoGeometry.QuantumContext.MarkovAttentionKemenyTrace

/-!
# Polarized attention return-cost order colimits

This module specializes the finite-horizon return-cost cocone to the actual
polarized Gibbs-row attention transition. It also identifies the stationary-
weighted sum of the cocone vertices with the group-inverse trace expression.
The cocones are order colimits of finite-horizon trajectory integrals.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovDrazin.PolarizedAttention

open CategoryTheory.Limits
open InfoGeometry.Canonical.Attention
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin
open InfoGeometry.QuantumContext.FiniteMarkovReturnTrajectoryColimit
open InfoGeometry.QuantumContext.FiniteMarkovTrajectorySuccessorLaw
open InfoGeometry.QuantumContext.MarkovDrazin
open InfoGeometry.QuantumContext.MarkovDrazin.Attention
open scoped BigOperators

variable {E V : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [AddCommMonoid V] [Module ℝ V]
variable {n : ℕ} [Fact (0 < n)]

local instance polarizedReturnColimitFinNonempty : Nonempty (Fin n) :=
  ⟨⟨0, Fact.out⟩⟩

/-- The categorical colimit cocone of the finite-horizon return-cost diagram
for the actual polarized Gibbs-row attention transition. -/
noncomputable def polarizedAttentionReturnTrajectoryColimitCocone
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ)
    (start target : Fin n) :
    ColimitCocone (trajectoryLawAfterStepCostDiagram
      (polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β)
      (polarizedPlusAttentionMatrix_mem_rowStochastic
        (E := E) (V := V) queries ctx β)
      target start) :=
  trajectoryLawAfterStepCostColimitCocone
    (polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β)
    (polarizedPlusAttentionMatrix_mem_rowStochastic
      (E := E) (V := V) queries ctx β)
    (polarizedPlusAttentionMatrix_pos (E := E) (V := V) queries ctx β)
    target start

/-- The vertex of the polarized return cocone is the established
group-inverse return-adjusted potential. -/
theorem polarizedAttentionReturnTrajectoryColimitCocone_pt_eq_potential
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ)
    (π : Fin n → ℝ) (hπnonneg : ∀ j, 0 ≤ π j)
    (hπsum : ∑ j, π j = 1)
    (hπstat : ∀ j, ∑ i, π i *
      polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β i j = π j)
    (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : IsGroupInverse
      (1 - polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β) G)
    (start target : Fin n) :
    (polarizedAttentionReturnTrajectoryColimitCocone
      (E := E) (V := V) queries ctx β start target).cocone.pt =
      groupInverseReturnAdjustedPotential π G start target := by
  change trajectoryLawAfterStepCostColimit
      (polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β)
      (polarizedPlusAttentionMatrix_mem_rowStochastic
        (E := E) (V := V) queries ctx β)
      target start = _
  exact trajectoryLawAfterStepCostColimit_eq_groupInverseReturnAdjustedPotential
    (polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β) G π
    (polarizedPlusAttentionMatrix_mem_rowStochastic
      (E := E) (V := V) queries ctx β)
    (polarizedPlusAttentionMatrix_pos (E := E) (V := V) queries ctx β)
    hπnonneg hπsum hπstat hG target start

/-- The stationary-weighted sum of the actual polarized return-colimit
cocone vertices is `trace G + 1`. This is the cocone-level integration of
the finite-return diagrams with the existing Kemeny trace identity. -/
theorem polarizedAttentionReturnTrajectoryColimit_vertices_sum_eq_trace_add_one
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ)
    (π : Fin n → ℝ) (hπnonneg : ∀ j, 0 ≤ π j)
    (hπsum : ∑ j, π j = 1)
    (hπstat : ∀ j, ∑ i, π i *
      polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β i j = π j)
    (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : IsGroupInverse
      (1 - polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β) G)
    (start : Fin n) :
    (∑ target ∈ Finset.univ, π target *
      (polarizedAttentionReturnTrajectoryColimitCocone
        (E := E) (V := V) queries ctx β start target).cocone.pt) =
      Matrix.trace G + 1 := by
  have hpotential (target : Fin n) :
      (polarizedAttentionReturnTrajectoryColimitCocone
        (E := E) (V := V) queries ctx β start target).cocone.pt =
        groupInverseReturnAdjustedPotential π G start target :=
    polarizedAttentionReturnTrajectoryColimitCocone_pt_eq_potential
      (E := E) (V := V) queries ctx β π hπnonneg hπsum hπstat G hG start target
  calc
    (∑ target ∈ Finset.univ, π target *
        (polarizedAttentionReturnTrajectoryColimitCocone
          (E := E) (V := V) queries ctx β start target).cocone.pt) =
      ∑ target ∈ Finset.univ,
        π target * groupInverseReturnAdjustedPotential π G start target := by
          apply Finset.sum_congr rfl
          intro target _
          rw [hpotential target]
    _ = Matrix.trace G + 1 :=
      weightedGroupInverseReturnAdjustedPotentialSum_eq_trace_add_one π G
        (fun j => (stationaryRowProbability_pos_of_pos_entries
          (polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β) π
          (polarizedPlusAttentionMatrix_pos (E := E) (V := V) queries ctx β)
          hπnonneg hπsum hπstat j).ne')
        (groupInverse_matrix_row_sum_eq_zero
          (polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β)
          G
          (polarizedPlusAttentionMatrix_mem_rowStochastic
            (E := E) (V := V) queries ctx β)
          hG)
        start

/-- Actual polarized attention admits a stationary row weight and a matrix
group inverse for which the stationary-weighted sum of return-colimit cocone
vertices is the Kemeny trace `trace G + 1`. The colimit values here are the
categorical cocone vertices defined above, not a separately introduced
trajectory supremum. -/
theorem exists_polarizedAttention_returnTrajectoryColimitKemenyTrace
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ)
    (start : Fin n) :
    ∃ π : Fin n → ℝ, ∃ G : Matrix (Fin n) (Fin n) ℝ,
      (∀ j, 0 < π j) ∧
      (∑ j, π j = 1) ∧
      (∀ j, ∑ i, π i *
        polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β i j = π j) ∧
      IsGroupInverse
        (1 - polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β) G ∧
      (∑ target ∈ Finset.univ, π target *
        (polarizedAttentionReturnTrajectoryColimitCocone
          (E := E) (V := V) queries ctx β start target).cocone.pt) =
        Matrix.trace G + 1 := by
  obtain ⟨π, G, hπpos, hπsum, hπstat, hG, _htrace⟩ :=
    exists_polarizedAttention_returnTrajectoryKemenyTrace
      (E := E) (V := V) queries ctx β start
  refine ⟨π, G, hπpos, hπsum, hπstat, hG, ?_⟩
  exact polarizedAttentionReturnTrajectoryColimit_vertices_sum_eq_trace_add_one
    (E := E) (V := V) queries ctx β π
    (fun j => le_of_lt (hπpos j)) hπsum hπstat G hG start

end InfoGeometry.QuantumContext.MarkovDrazin.PolarizedAttention

end noncomputable section
