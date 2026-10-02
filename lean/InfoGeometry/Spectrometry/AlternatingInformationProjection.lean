import InfoGeometry.Spectrometry.MatrixFixedScaleLeastSquares
import InfoGeometry.Spectrometry.ThermodynamicTransportPipeline
import Mathlib.Topology.Order.MonotoneConvergence

namespace InfoGeometry.Spectrometry.AlternatingInformationProjection

open scoped BigOperators Topology
open Filter Finset FixedScaleLeastSquares MatrixFixedScaleLeastSquares
open AitchisonGeometricMedian ThermodynamicTransportPipeline

namespace MatrixDualityDependency

inductive Archetype
  | totalLossDefinition
  | matrixPythagoreanIdentity
  | globalProfileMinimizer
  | uniqueProfileCharacterization
  | lossLowerBoundedness
  | scaleDescentContract
  | sequenceInfimumConvergence
  deriving DecidableEq, Fintype

open Archetype

def prerequisites : Archetype → Finset Archetype
  | totalLossDefinition => {totalLossDefinition}
  | matrixPythagoreanIdentity => {totalLossDefinition, matrixPythagoreanIdentity}
  | globalProfileMinimizer =>
      {totalLossDefinition, matrixPythagoreanIdentity, globalProfileMinimizer}
  | uniqueProfileCharacterization =>
      {totalLossDefinition, matrixPythagoreanIdentity, uniqueProfileCharacterization}
  | lossLowerBoundedness => {totalLossDefinition, lossLowerBoundedness}
  | scaleDescentContract => {totalLossDefinition, scaleDescentContract}
  | sequenceInfimumConvergence =>
      {totalLossDefinition, matrixPythagoreanIdentity, globalProfileMinimizer,
        lossLowerBoundedness, scaleDescentContract, sequenceInfimumConvergence}

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

instance : DecidableLE Archetype := fun earlier later =>
  inferInstanceAs (Decidable (prerequisites earlier ⊆ prerequisites later))

theorem dependency_branches :
    totalLossDefinition ≤ matrixPythagoreanIdentity ∧
    matrixPythagoreanIdentity ≤ globalProfileMinimizer ∧
    matrixPythagoreanIdentity ≤ uniqueProfileCharacterization ∧
    totalLossDefinition ≤ lossLowerBoundedness ∧
    globalProfileMinimizer ≤ sequenceInfimumConvergence ∧
    lossLowerBoundedness ≤ sequenceInfimumConvergence ∧
    scaleDescentContract ≤ sequenceInfimumConvergence := by decide

theorem uniqueness_and_boundedness_incomparable :
    ¬ uniqueProfileCharacterization ≤ lossLowerBoundedness ∧
      ¬ lossLowerBoundedness ≤ uniqueProfileCharacterization := by decide

theorem profile_and_scale_descent_incomparable :
    ¬ globalProfileMinimizer ≤ scaleDescentContract ∧
      ¬ scaleDescentContract ≤ globalProfileMinimizer := by decide

end MatrixDualityDependency

noncomputable section

variable {rowCount acquisitionCount : ℕ}

def profileProjectionStep
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (scales : Fin acquisitionCount → ℝ) : Fin rowCount → ℝ :=
  optimalProfile observed scales

theorem projection_step_decreases_loss
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (scales : Fin acquisitionCount → ℝ) (profile : Fin rowCount → ℝ)
    (norm_ne : scaleSquareSum scales ≠ 0) :
    totalLoss observed scales (profileProjectionStep observed scales) ≤
      totalLoss observed scales profile :=
  total_loss_minimizes observed scales profile norm_ne

theorem projection_losses_antitone
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (scales : ℕ → Fin acquisitionCount → ℝ) (profiles : ℕ → Fin rowCount → ℝ)
    (norm_ne : ∀ step, scaleSquareSum (scales step) ≠ 0)
    (profile_update : ∀ step,
      profiles (step + 1) = profileProjectionStep observed (scales step))
    (scale_descent : ∀ step,
      totalLoss observed (scales (step + 1)) (profiles (step + 1)) ≤
        totalLoss observed (scales step) (profiles (step + 1))) :
    Antitone (fun step => totalLoss observed (scales step) (profiles step)) := by
  apply antitone_nat_of_succ_le
  intro step
  have profile_descent := projection_step_decreases_loss observed (scales step)
    (profiles step) (norm_ne step)
  rw [← profile_update step] at profile_descent
  exact (scale_descent step).trans profile_descent

theorem loss_sequence_converges_to_sequence_infimum
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (scales : ℕ → Fin acquisitionCount → ℝ) (profiles : ℕ → Fin rowCount → ℝ)
    (descent : Antitone (fun step => totalLoss observed (scales step) (profiles step))) :
    Tendsto (fun step => totalLoss observed (scales step) (profiles step)) atTop
      (𝓝 (⨅ step, totalLoss observed (scales step) (profiles step))) := by
  apply tendsto_atTop_ciInf descent
  refine ⟨0, ?_⟩
  rintro value ⟨step, rfl⟩
  exact total_loss_nonneg observed (scales step) (profiles step)

theorem projection_loss_sequence_converges
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (scales : ℕ → Fin acquisitionCount → ℝ) (profiles : ℕ → Fin rowCount → ℝ)
    (norm_ne : ∀ step, scaleSquareSum (scales step) ≠ 0)
    (profile_update : ∀ step,
      profiles (step + 1) = profileProjectionStep observed (scales step))
    (scale_descent : ∀ step,
      totalLoss observed (scales (step + 1)) (profiles (step + 1)) ≤
        totalLoss observed (scales step) (profiles (step + 1))) :
    Tendsto (fun step => totalLoss observed (scales step) (profiles step)) atTop
      (𝓝 (⨅ step, totalLoss observed (scales step) (profiles step))) :=
  loss_sequence_converges_to_sequence_infimum observed scales profiles
    (projection_losses_antitone observed scales profiles norm_ne profile_update scale_descent)

def centeredProfileLoss
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (center : aitchisonSpace acquisitionCount) : ℝ :=
  totalLoss observed (acquisitionScales center) (optimalProfile observed (acquisitionScales center))

def guardedCenterStep
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (current proposal : aitchisonSpace acquisitionCount) : aitchisonSpace acquisitionCount :=
  if totalLoss observed (acquisitionScales proposal)
      (optimalProfile observed (acquisitionScales current)) ≤ centeredProfileLoss observed current
    then proposal else current

theorem guarded_center_fixed_profile_descent
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (current proposal : aitchisonSpace acquisitionCount) :
    totalLoss observed (acquisitionScales (guardedCenterStep observed current proposal))
      (optimalProfile observed (acquisitionScales current)) ≤ centeredProfileLoss observed current := by
  unfold guardedCenterStep
  split_ifs with accepted
  · exact accepted
  · exact le_rfl

theorem guarded_center_profile_loss_descent
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (current proposal : aitchisonSpace acquisitionCount) (count_pos : 0 < acquisitionCount) :
    centeredProfileLoss observed (guardedCenterStep observed current proposal) ≤
      centeredProfileLoss observed current := by
  exact (total_loss_minimizes observed
    (acquisitionScales (guardedCenterStep observed current proposal))
    (optimalProfile observed (acquisitionScales current))
    (ne_of_gt (acquisition_scales_norm_pos _ count_pos))).trans
      (guarded_center_fixed_profile_descent observed current proposal)

def guardedCenterIterate
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (propose : ℕ → aitchisonSpace acquisitionCount → aitchisonSpace acquisitionCount)
    (initial : aitchisonSpace acquisitionCount) : ℕ → aitchisonSpace acquisitionCount
  | 0 => initial
  | step + 1 =>
      let current := guardedCenterIterate observed propose initial step
      guardedCenterStep observed current (propose step current)

theorem guarded_iterate_scales_product
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (propose : ℕ → aitchisonSpace acquisitionCount → aitchisonSpace acquisitionCount)
    (initial : aitchisonSpace acquisitionCount) (step : ℕ) :
    (∏ acquisition,
      acquisitionScales (guardedCenterIterate observed propose initial step) acquisition) = 1 :=
  acquisition_scales_product _

theorem guarded_losses_antitone
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (propose : ℕ → aitchisonSpace acquisitionCount → aitchisonSpace acquisitionCount)
    (initial : aitchisonSpace acquisitionCount) (count_pos : 0 < acquisitionCount) :
    Antitone (fun step =>
      centeredProfileLoss observed (guardedCenterIterate observed propose initial step)) := by
  apply antitone_nat_of_succ_le
  intro step
  exact guarded_center_profile_loss_descent observed _ _ count_pos

theorem guarded_losses_converge_to_sequence_infimum
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (propose : ℕ → aitchisonSpace acquisitionCount → aitchisonSpace acquisitionCount)
    (initial : aitchisonSpace acquisitionCount) (count_pos : 0 < acquisitionCount) :
    Tendsto (fun step =>
      centeredProfileLoss observed (guardedCenterIterate observed propose initial step)) atTop
      (𝓝 (⨅ step,
        centeredProfileLoss observed (guardedCenterIterate observed propose initial step))) :=
  loss_sequence_converges_to_sequence_infimum observed _ _
    (guarded_losses_antitone observed propose initial count_pos)

end

end InfoGeometry.Spectrometry.AlternatingInformationProjection
