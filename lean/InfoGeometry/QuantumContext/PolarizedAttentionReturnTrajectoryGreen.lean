/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.PolarizedAttentionTrajectoryGreen
import InfoGeometry.QuantumContext.FiniteMarkovReturnTrajectoryGreen

/-!
# Polarized attention first-return trajectory Green theorem

The generic finite first-return result is specialized to the actual polarized
Gibbs-row attention matrix. Stationarity and the matrix group inverse are
obtained from their existing owners. The conclusion concerns the order
supremum of finite-horizon integrals, not an infinite-path expectation.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovDrazin.PolarizedAttention

open InfoGeometry.Canonical.Attention
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin
open InfoGeometry.QuantumContext.FiniteMarkovTrajectorySuccessorLaw
open InfoGeometry.QuantumContext.FiniteMarkovReturnTrajectoryGreen
open InfoGeometry.QuantumContext.MarkovDrazin
open InfoGeometry.QuantumContext.MarkovDrazin.Attention

variable {E V : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [AddCommMonoid V] [Module ℝ V]
variable {n : ℕ} [Fact (0 < n)]

local instance polarizedReturnFinNonempty : Nonempty (Fin n) :=
  ⟨⟨0, Fact.out⟩⟩

/-- Every actual polarized Gibbs-row attention matrix admits a positive
normalized stationary row weight and a matrix group inverse for which the
finite first-passage-after-step trajectory integrals have supremum equal to
the return-adjusted Green potential. In particular, this includes the
diagonal first-return value. -/
theorem exists_polarizedAttention_returnTrajectoryGreen
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ)
    (start target : Fin n) :
    ∃ π : Fin n → ℝ, ∃ G : Matrix (Fin n) (Fin n) ℝ,
      (∀ j, 0 < π j) ∧
      (∑ j, π j = 1) ∧
      (∀ j, ∑ i, π i *
        polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β i j = π j) ∧
      IsGroupInverse
        (1 - polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β) G ∧
      sSup (Set.range (fun horizon =>
        ∫ path, pathFirstPassageAfterStepCost target horizon start path ∂
          finiteTrajectorySuccessorLaw
            (polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β)
            (polarizedPlusAttentionMatrix_mem_rowStochastic
              (E := E) (V := V) queries ctx β)
            horizon start)) =
        groupInverseReturnAdjustedPotential π G start target := by
  obtain ⟨π, hπ, _hπunique⟩ :=
    existsUnique_positive_normalized_stationary_row
      (E := E) (V := V) queries ctx β
  rcases hπ with ⟨hπpos, hπsum, hπstat⟩
  obtain ⟨G, hG⟩ :=
    exists_polarizedAttention_matrix_groupInverse
      (E := E) (V := V) queries ctx β
  refine ⟨π, G, hπpos, hπsum, hπstat, hG, ?_⟩
  exact trajectoryLaw_afterStepCost_sup_eq_groupInverseReturnAdjustedPotential
    (polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β) G π
    (polarizedPlusAttentionMatrix_mem_rowStochastic
      (E := E) (V := V) queries ctx β)
    (polarizedPlusAttentionMatrix_pos (E := E) (V := V) queries ctx β)
    (fun j => le_of_lt (hπpos j)) hπsum hπstat hG target start

end InfoGeometry.QuantumContext.MarkovDrazin.PolarizedAttention

end noncomputable section
