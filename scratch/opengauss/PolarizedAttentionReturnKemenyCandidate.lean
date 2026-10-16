/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.PolarizedAttentionReturnTrajectoryGreen
import InfoGeometry.QuantumContext.MarkovAttentionKemenyTrace

/-!
# Candidate: polarized-attention first-return Kemeny identity

This candidate joins the existing finite-horizon first-return trajectory
supremum theorem to the existing algebraic group-inverse trace identity. The
result is a finite sum of order suprema of finite-horizon integrals. It does
not identify these quantities with expectations on an infinite path space.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovDrazin.PolarizedAttention

open InfoGeometry.Canonical.Attention
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin
open InfoGeometry.QuantumContext.FiniteMarkovTrajectorySuccessorLaw
open InfoGeometry.QuantumContext.FiniteMarkovReturnTrajectoryGreen
open InfoGeometry.QuantumContext.MarkovDrazin
open InfoGeometry.QuantumContext.MarkovDrazin.Attention
open scoped BigOperators

variable {E V : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [AddCommMonoid V] [Module ℝ V]
variable {n : ℕ} [Fact (0 < n)]

local instance polarizedReturnKemenyFinNonempty : Nonempty (Fin n) :=
  ⟨⟨0, Fact.out⟩⟩

/-- For one fixed stationary row and group inverse, summing the targetwise
finite first-return trajectory suprema gives the algebraic Kemeny trace
`trace G + 1`. Each targetwise supremum is supplied by the finite trajectory
Green theorem, and the final finite sum is the existing group-inverse trace
identity. -/
theorem polarizedAttention_returnTrajectorySupSum_eq_trace_add_one
    (queries : Fin n → E) (ctx : ContextWindow n E V) (β : ℝ)
    (π : Fin n → ℝ)
    (hπpos : ∀ j, 0 < π j)
    (hπsum : ∑ j, π j = 1)
    (hπstat : ∀ j, ∑ i, π i *
      polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β i j = π j)
    (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : IsGroupInverse
      (1 - polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β) G)
    (start : Fin n) :
    ∑ target ∈ Finset.univ, π target *
      sSup (Set.range (fun horizon =>
        ∫ path, pathFirstPassageAfterStepCost target horizon start path ∂
          finiteTrajectorySuccessorLaw
            (polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β)
            (polarizedPlusAttentionMatrix_mem_rowStochastic
              (E := E) (V := V) queries ctx β)
            horizon start)) = Matrix.trace G + 1 := by
  let P : Matrix (Fin n) (Fin n) ℝ :=
    polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β
  have hP : P ∈ Matrix.rowStochastic ℝ (Fin n) := by
    exact polarizedPlusAttentionMatrix_mem_rowStochastic
      (E := E) (V := V) queries ctx β
  have hPpos : ∀ i j, 0 < P i j := by
    intro i j
    exact polarizedPlusAttentionMatrix_pos (E := E) (V := V) queries ctx β i j
  have hG' : IsGroupInverse (1 - P) G := by
    simpa [P] using hG
  have htraj (target : Fin n) :
      sSup (Set.range (fun horizon =>
        ∫ path, pathFirstPassageAfterStepCost target horizon start path ∂
          finiteTrajectorySuccessorLaw P hP horizon start)) =
        groupInverseReturnAdjustedPotential π G start target := by
    exact trajectoryLaw_afterStepCost_sup_eq_groupInverseReturnAdjustedPotential
      P G π hP hPpos (fun j => le_of_lt (hπpos j)) hπsum hπstat hG'
      target start
  calc
    (∑ target ∈ Finset.univ, π target *
        sSup (Set.range (fun horizon =>
          ∫ path, pathFirstPassageAfterStepCost target horizon start path ∂
            finiteTrajectorySuccessorLaw
              (polarizedPlusAttentionMatrix (E := E) (V := V) queries ctx β)
              (polarizedPlusAttentionMatrix_mem_rowStochastic
                (E := E) (V := V) queries ctx β)
              horizon start))) =
        ∑ target ∈ Finset.univ, π target *
          groupInverseReturnAdjustedPotential π G start target := by
            apply Finset.sum_congr rfl
            intro target htarget
            rw [htraj target]
            simp [P, hP]
    _ = Matrix.trace G + 1 := by
      simpa using weightedGroupInverseReturnAdjustedPotentialSum_eq_trace_add_one
        π G (fun j => (hπpos j).ne')
        (groupInverse_matrix_row_sum_eq_zero P G hP hG') start

/-- Every actual polarized Gibbs-row attention matrix admits a positive
normalized stationary row, a matrix group inverse, and the finite-sum
first-return Kemeny trace identity. The statement is a finite algebraic
order-supremum identity, not an infinite-path expectation theorem. -/
theorem exists_polarizedAttention_returnTrajectoryKemenyIdentity
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
  exact polarizedAttention_returnTrajectorySupSum_eq_trace_add_one
    queries ctx β π hπpos hπsum hπstat G hG start

end InfoGeometry.QuantumContext.MarkovDrazin.PolarizedAttention

end noncomputable section
