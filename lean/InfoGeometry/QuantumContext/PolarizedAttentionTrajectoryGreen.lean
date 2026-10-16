/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.PolarizedAttentionMarkovDrazin
import InfoGeometry.QuantumContext.FiniteMarkovTrajectoryHittingGreen
import InfoGeometry.QuantumContext.MarkovAttentionKemenyTrace

/-!
# Polarized attention trajectory Green trace

This module connects the actual finite polarized Gibbs attention transition
to the existing finite-horizon trajectory order-colimit and group-inverse
trace theorem. The conclusion is an order-colimit of finite-horizon path
integrals, not an expectation on an infinite path space.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovDrazin.PolarizedAttention

open InfoGeometry.Canonical.Attention
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin
open InfoGeometry.QuantumContext.FiniteMarkovTrajectoryHittingGreen
open InfoGeometry.QuantumContext.FiniteMarkovHittingPMFExpectation
open InfoGeometry.QuantumContext.FiniteMarkovTrajectorySuccessorLaw
open InfoGeometry.QuantumContext.MarkovDrazin.Attention
open scoped BigOperators

variable {E V : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [AddCommMonoid V] [Module ℝ V]
variable {n : ℕ} [Fact (0 < n)]

local instance trajectoryGreenFinNonempty : Nonempty (Fin n) :=
  ⟨⟨0, Fact.out⟩⟩

/-- The group inverse of the polarized attention Laplacian can be represented
as a matrix in the standard finite coordinate basis. -/
theorem exists_polarizedAttention_matrix_groupInverse
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ) :
    ∃ G : Matrix (Fin n) (Fin n) ℝ,
      IsGroupInverse
        (1 - polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β) G := by
  obtain ⟨D, hD⟩ :=
    InfoGeometry.QuantumContext.MarkovDrazin.Attention.exists_polarizedAttention_laplacian_groupInverse
      (E := E) (V := V) queries ctx β
  let G : Matrix (Fin n) (Fin n) ℝ := LinearMap.toMatrix' D
  have hG : IsGroupInverse
      (1 - polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β) G := by
    refine ⟨?_, ?_, ?_⟩
    · apply Matrix.toLin'.injective
      simpa [G, Matrix.toLin'_mul, Module.End.mul_eq_comp] using hD.1
    · apply Matrix.toLin'.injective
      simpa [G, Matrix.toLin'_mul, Module.End.mul_eq_comp] using hD.2.1
    · apply Matrix.toLin'.injective
      simpa [G, Matrix.toLin'_mul, Module.End.mul_eq_comp] using hD.2.2
  exact ⟨G, hG⟩

/-- For the actual polarized attention transition, the stationary-weighted
sum over all targets of finite-horizon first-hit trajectory costs has order
colimit equal to the trace of any supplied group inverse of `1 - P`.

Here `P` is row stochastic and strictly positive. The stationary equation is
`∑ i, π i * P i j = π j`, while `P` acts on column observables. -/
theorem polarizedAttention_trajectoryLaw_weightedHittingCostColimit_eq_groupInverseTrace
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ)
    (π : Fin n → ℝ) (hπnonneg : ∀ j, 0 ≤ π j)
    (hπsum : ∑ j, π j = 1)
    (hπstat : ∀ j, ∑ i, π i *
      polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β i j = π j)
    (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : IsGroupInverse
      (1 - polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β) G)
    (start : Fin n) :
    sSup (Set.range (fun horizon =>
      ∑ target ∈ Finset.univ, π target *
        ∫ path, pathFirstHitCost target horizon start path ∂
          finiteTrajectorySuccessorLaw
            (polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β)
            (polarizedPlusAttentionMatrix_mem_rowStochastic
              (E := E) (V := V) queries ctx β)
            horizon start)) = Matrix.trace G := by
  exact trajectoryLaw_weightedHittingCostColimit_eq_groupInverseTrace
    (polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β) G π
    (polarizedPlusAttentionMatrix_mem_rowStochastic
      (E := E) (V := V) queries ctx β)
    (polarizedPlusAttentionMatrix_pos (E := E) (V := V) queries ctx β)
    hπnonneg hπsum hπstat hG start

/-- For the actual polarized Gibbs attention matrix, the stationary-weighted
return-adjusted group-inverse potential sums to `trace G + 1`. This is the
algebraic diagonal-correction identity; it makes no pathwise first-return
claim. -/
theorem polarizedAttention_returnAdjustedPotentialSum_eq_trace_add_one
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ)
    (π : Fin n → ℝ) (hπnonneg : ∀ j, 0 ≤ π j)
    (hπsum : ∑ j, π j = 1)
    (hπstat : ∀ j, ∑ i, π i *
      polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β i j = π j)
    (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : IsGroupInverse
      (1 - polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β) G)
    (start : Fin n) :
    ∑ target ∈ Finset.univ, π target *
      InfoGeometry.QuantumContext.MarkovDrazin.groupInverseReturnAdjustedPotential
        π G start target = Matrix.trace G + 1 := by
  have hπpos :=
    InfoGeometry.QuantumContext.MarkovDrazin.stationaryRowProbability_pos_of_pos_entries
      (polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β) π
      (polarizedPlusAttentionMatrix_pos (E := E) (V := V) queries ctx β)
      hπnonneg hπsum hπstat
  apply InfoGeometry.QuantumContext.MarkovDrazin.weightedGroupInverseReturnAdjustedPotentialSum_eq_trace_add_one
  · intro j
    exact (hπpos j).ne'
  · exact InfoGeometry.QuantumContext.MarkovDrazin.groupInverse_matrix_row_sum_eq_zero
      (polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β)
      G
      (polarizedPlusAttentionMatrix_mem_rowStochastic
        (E := E) (V := V) queries ctx β)
      hG

end InfoGeometry.QuantumContext.MarkovDrazin.PolarizedAttention

end noncomputable section
