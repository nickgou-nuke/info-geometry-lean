import InfoGeometry.MassSpectrometry.FragmentationResponseEvidence

/-!
# Exact finite-absorption fixtures and boundary checks

Concrete non-diagonal chains expose the final absorption step. A positive
self-loop illustrates why small numerical support leakage cannot be silently
covered by the exact finite-cutoff theorem. All examples use kernel proofs.
-/

noncomputable section
namespace InfoGeometry.MassSpectrometry.FiniteFragmentAbsorptionAudit
open scoped BigOperators Matrix
open InfoGeometry.SignedNetwork.RankedDAGResolvent
open InfoGeometry.Algebra.RankedMatrixPowers

/-- Three original states: 2 -> 1 -> 0, followed by absorption. -/
def chainDAG : FragmentationDAG 3 where
  edge u v := u.val = v.val + 1
  rank u := u.val
  rank_decreases := by intro u v h; omega

def chainGrammar : StochasticGrammar chainDAG where
  weight u v := if u.val = v.val + 1 then 1 else 0
  weight_nonneg := by intro u v; split_ifs <;> norm_num
  support := by
    intro u v h
    change u.val = v.val + 1
    by_contra hn
    simp [hn] at h
  row_sum_le_one := by
    intro u
    simp only [Fin.sum_univ_succ]
    fin_cases u <;> norm_num

theorem chain_transient_cube : chainGrammar.transientMatrix ^ 3 = 0 :=
  chainGrammar.transient_pow_eq_zero_of_rank_bound 3 (fun u => u.isLt)

theorem chain_absorbs_in_three :
    chainGrammar.absorbingCompletion ^ 3 = absorptionProjection 3 :=
  chainGrammar.absorbingCompletion_pow_eq_projection_of_transient_zero 3 chain_transient_cube

/-- Two steps reach the last original vertex, not the absorbing state. -/
theorem chain_not_absorbed_in_two :
    chainGrammar.absorbingCompletion ^ 2 ≠ absorptionProjection 3 := by
  intro h
  have hentry := congrArg (fun M => M (some (2 : Fin 3)) (some (0 : Fin 3))) h
  norm_num [pow_two, Matrix.mul_apply, Fintype.sum_option, Fin.sum_univ_succ,
    StochasticGrammar.absorbingCompletion, StochasticGrammar.terminalWeight,
    chainGrammar, absorptionProjection] at hentry

theorem chain_fundamental_explicit :
    chainGrammar.fundamentalMatrix = !![1, 0, 0; 1, 1, 0; 1, 1, 1] := by
  have h := FiniteGreenResponse.horizon_independent chainGrammar.transientMatrix
    (rankHorizon chainDAG.rank) 3 chainGrammar.transient_pow_rankHorizon_eq_zero
    chain_transient_cube
  change finiteGreen chainGrammar.transientMatrix (rankHorizon chainDAG.rank) = _
  rw [h]
  simp only [finiteGreen, Finset.sum_range_succ, Finset.sum_range_zero,
    pow_zero, pow_one, pow_two, zero_add]
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_succ]
  fin_cases i <;> fin_cases j <;>
    norm_num [StochasticGrammar.transientMatrix, chainGrammar]

theorem chain_occupancy_explicit : chainGrammar.occupancyPotential = ![1, 2, 3] := by
  rw [StochasticGrammar.occupancyPotential, chain_fundamental_explicit]
  ext i
  fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Every completed chain keeps its absorbing row forever. -/
theorem completed_power_ne_zero {n : ℕ} {D : FragmentationDAG n}
    (G : StochasticGrammar D) (m : ℕ) : G.absorbingCompletion ^ m ≠ 0 := by
  intro hz
  have h := G.absorbingCompletion_pow_none m none
  rw [hz] at h
  norm_num at h

/-- A rank-zero terminal original vertex still needs one step. -/
theorem terminal_original_ne_absorbed_at_zero :
    (1 : Matrix (Option (Fin 1)) (Option (Fin 1)) ℝ) ≠ absorptionProjection 1 := by
  intro h
  have hentry := congrArg (fun M => M (some (0 : Fin 1)) none) h
  norm_num [absorptionProjection] at hentry

def leakingTransient : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 1 / 2

theorem leaking_power_entry (m : ℕ) :
    (leakingTransient ^ m) 0 0 = (1 / 2 : ℝ) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [pow_succ, Matrix.mul_apply, Fin.sum_univ_one, leakingTransient]
      rw [ih]

/-- A positive self-loop never has an exact finite cutoff. -/
theorem leaking_power_ne_zero (m : ℕ) : leakingTransient ^ m ≠ 0 := by
  intro hz
  have h := leaking_power_entry m
  rw [hz] at h
  have hn : (1 / 2 : ℝ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  exact hn h.symm

#check InfoGeometry.Algebra.RankedMatrixPowers.pow_entry_eq_zero_of_rank_lt
#check StochasticGrammar.absorbingCompletion_stabilizes
#check StochasticGrammar.absorbingCompletion_absorbed_after_rank
#check FiniteGreenResponse.oneSubUnit
#check StochasticGrammar.response_unique
#check StochasticGrammar.occupancyPotential_bounds
#check StochasticGrammar.fundamentalMatrix_difference_norm_le
#check StochasticGrammar.response_uniformErrorBound
#check FragmentationResponseEvidence.responseModelError
#check FragmentationResponseEvidence.robust_identification_from_transition_error

end InfoGeometry.MassSpectrometry.FiniteFragmentAbsorptionAudit
