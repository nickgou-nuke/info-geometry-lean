import InfoGeometry.MassSpectrometry.MolecularExperimentEvidence
import InfoGeometry.MassSpectrometry.PartialPeakAssignment
import InfoGeometry.MassSpectrometry.TerminatingFragmentation

/-! Exact, non-vacuous fixtures and explicit failure-boundary examples. -/

noncomputable section
namespace InfoGeometry.MassSpectrometry.ExperimentalEvidenceAudit
open ExperimentalObservation
open scoped BigOperators

private def singlyCharged : IonInterpretation := ⟨1, by norm_num, 0⟩
private def doublyCharged : IonInterpretation := ⟨2, by norm_num, 0⟩

/-- Lower m/z need not mean lower neutral mass when charge changes. -/
theorem mz_order_is_not_neutral_mass_order :
    (75 : ℝ) < 100 ∧
      singlyCharged.neutralMass 100 < doublyCharged.neutralMass 75 := by
  norm_num [singlyCharged, doublyCharged, IonInterpretation.neutralMass,
    IonInterpretation.chargeMagnitude]

theorem rational_peak_checker_accepts :
    (RationalPeakRecord.mk (101 / 2) (7 / 3)).check = true := by decide

theorem rational_peak_checker_rejects_zero_mz :
    (RationalPeakRecord.mk 0 1).check = false := by decide

theorem rational_peak_checker_rejects_negative_intensity :
    (RationalPeakRecord.mk 1 (-1)).check = false := by decide

/-- Two observed peaks, three candidates, explicit unmatched capacities. -/
def rectangularPlan : PartialPeakAssignment (Fin 2) (Fin 3) where
  weight := !![(1 / 2 : ℝ), 0, 0; 0, 1, 0]
  peakCapacity := fun _ => 1
  fragmentCapacity := fun _ => 1
  nonneg := by intro i j; fin_cases i <;> fin_cases j <;> norm_num
  row_le := by intro i; fin_cases i <;> norm_num [Fin.sum_univ_three]
  col_le := by intro j; fin_cases j <;> norm_num [Fin.sum_univ_two]

theorem rectangular_residuals :
    rectangularPlan.unmatchedPeak 0 = 1 / 2 ∧
    rectangularPlan.unmatchedPeak 1 = 0 ∧
    rectangularPlan.undetectedFragment 2 = 1 := by
  norm_num [rectangularPlan, PartialPeakAssignment.unmatchedPeak,
    PartialPeakAssignment.undetectedFragment, Fin.sum_univ_two, Fin.sum_univ_three]

def twoVertexDAG : FragmentationDAG 2 where
  edge u v := v.val < u.val
  rank u := u.val
  rank_decreases := by intro u v h; exact h

def terminatingHalfGrammar : StochasticGrammar twoVertexDAG where
  weight u v := if u = 1 ∧ v = 0 then 1 / 2 else 0
  weight_nonneg := by intro u v; split_ifs <;> norm_num
  support := by
    intro u v h
    have hc : u = 1 ∧ v = 0 := by
      by_contra hn
      simp [hn] at h
    rcases hc with ⟨rfl, rfl⟩
    norm_num [twoVertexDAG]
  row_sum_le_one := by
    intro u
    fin_cases u <;> norm_num [Fin.sum_univ_two]

theorem terminal_and_absorbing_rows :
    terminatingHalfGrammar.terminalWeight 0 = 1 ∧
    terminatingHalfGrammar.terminalWeight 1 = 1 / 2 ∧
    terminatingHalfGrammar.absorbingCompletion (some 1) none = 1 / 2 ∧
    terminatingHalfGrammar.absorbingCompletion none none = 1 := by
  norm_num [terminatingHalfGrammar, StochasticGrammar.terminalWeight,
    StochasticGrammar.absorbingCompletion, Fin.sum_univ_two]

theorem strict_normalization_impossible : ¬ Nonempty (NormalizedGrammar twoVertexDAG) := by
  rintro ⟨G⟩
  exact no_normalized_strict_grammar G

def twoCandidates : MultiEnergyForwardModel Bool Bool ℝ where
  observe e a := if e then (if a then 4 else 0) else 0

def equalityChemistry : Setoid Bool where
  r := Eq
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

theorem one_informative_condition_separates :
    twoCandidates.RobustlySeparatesOn equalityChemistry Set.univ {true} 1 := by
  intro a _ b _ hne
  refine ⟨true, by simp, ?_⟩
  cases a <;> cases b <;>
    norm_num [twoCandidates, equalityChemistry, Real.dist_eq] at *

theorem uninformative_condition_identifies_nothing :
    twoCandidates.observe false false = twoCandidates.observe false true ∧
    ¬ equalityChemistry.r false true := by
  simp [twoCandidates, equalityChemistry]

/-- At exactly twice the radius, two closed error balls can intersect. -/
theorem strict_margin_is_necessary :
    dist (0 : ℝ) 1 ≤ 1 ∧ dist (2 : ℝ) 1 ≤ 1 ∧
      dist (0 : ℝ) 2 = 2 * 1 ∧ (0 : ℝ) ≠ 2 := by
  norm_num [Real.dist_eq]

#check IonInterpretation.neutralMass_mz_roundTrip
#check RationalPeakRecord.check_iff
#check PartialPeakAssignment.residual_mass_balance
#check PartialPeakAssignment.softAssignment_of_no_residual
#check StochasticGrammar.absorbingCompletion_row_sum
#check no_normalized_strict_grammar
#check NumericalEvidence.UniformErrorBound.comp
#check MultiEnergyForwardModel.exists_finite_identifying_experiment
#check MultiEnergyForwardModel.robust_identification_of_uniform_refinement
#check MolecularExperimentEvidence.robust_molecular_identification

end InfoGeometry.MassSpectrometry.ExperimentalEvidenceAudit
