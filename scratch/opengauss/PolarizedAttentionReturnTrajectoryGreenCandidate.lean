/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.PolarizedAttentionTrajectoryGreen
import InfoGeometry.QuantumContext.FiniteMarkovReturnTrajectoryGreen

/-!
# Existential first-return Green theorem for polarized attention

This candidate specializes the generic finite-horizon theorem to the actual
polarized Gibbs-row attention matrix. Unlike a wrapper with supplied stationary
and group-inverse witnesses, the result obtains both witnesses from the
existing polarized-attention owners.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovDrazin.PolarizedAttention

open InfoGeometry.Canonical.Attention
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin
open InfoGeometry.QuantumContext.FiniteMarkovTrajectorySuccessorLaw
open InfoGeometry.QuantumContext.FiniteMarkovReturnTrajectoryGreen
open InfoGeometry.QuantumContext.MarkovDrazin

variable {E V : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [AddCommMonoid V] [Module ℝ V]
variable {n : ℕ} [Fact (0 < n)]

local instance polarizedReturnFinNonempty : Nonempty (Fin n) :=
  ⟨⟨0, Fact.out⟩⟩

/-- Every actual polarized Gibbs-row attention matrix admits a normalized
positive stationary row weight and a matrix group inverse whose finite
after-step trajectory cost supremum equals the return-adjusted Green
potential. The witnesses are obtained from the existing actual-attention
stationarity and group-inverse existence theorems; no limiting path-space
expectation is asserted. -/
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
