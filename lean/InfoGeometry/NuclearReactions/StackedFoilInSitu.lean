import InfoGeometry.NuclearReactions.ActivationKinetics
import InfoGeometry.NuclearReactions.InSituCascadeCalibration
import InfoGeometry.NuclearReactions.FoilAlignment

namespace InfoGeometry.NuclearReactions.StackedFoilInSitu

open ActivationKinetics InSituCascadeCalibration FoilAlignment
open InfoGeometry.Probability.DetectorCopulaDecoupling

namespace ProofDependency

inductive Archetype
  | activationModel
  | rateRestoration
  | cascadeModel
  | efficiencyRatio
  | distanceModel
  | activityReconstruction
  | crossSectionRecovery
  | offsetRecovery
  | measurementChain
  deriving DecidableEq, Fintype

open Archetype

def prerequisites : Archetype → Finset Archetype
  | activationModel => {activationModel}
  | rateRestoration => {rateRestoration}
  | cascadeModel => {cascadeModel}
  | efficiencyRatio => {efficiencyRatio}
  | distanceModel => {distanceModel}
  | activityReconstruction => {rateRestoration, cascadeModel, efficiencyRatio, activityReconstruction}
  | crossSectionRecovery =>
      {activationModel, rateRestoration, cascadeModel, efficiencyRatio,
        activityReconstruction, crossSectionRecovery}
  | offsetRecovery => {distanceModel, offsetRecovery}
  | measurementChain => Finset.univ

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

theorem dependency_edges :
    rateRestoration ≤ activityReconstruction ∧ cascadeModel ≤ activityReconstruction ∧
    efficiencyRatio ≤ activityReconstruction ∧ activityReconstruction ≤ crossSectionRecovery ∧
    activationModel ≤ crossSectionRecovery ∧ distanceModel ≤ offsetRecovery ∧
    crossSectionRecovery ≤ measurementChain ∧ offsetRecovery ≤ measurementChain := by
  change prerequisites rateRestoration ⊆ prerequisites activityReconstruction ∧
    prerequisites cascadeModel ⊆ prerequisites activityReconstruction ∧
    prerequisites efficiencyRatio ⊆ prerequisites activityReconstruction ∧
    prerequisites activityReconstruction ⊆ prerequisites crossSectionRecovery ∧
    prerequisites activationModel ⊆ prerequisites crossSectionRecovery ∧
    prerequisites distanceModel ⊆ prerequisites offsetRecovery ∧
    prerequisites crossSectionRecovery ⊆ prerequisites measurementChain ∧
    prerequisites offsetRecovery ⊆ prerequisites measurementChain
  decide

theorem cross_section_and_alignment_incomparable :
    ¬ crossSectionRecovery ≤ offsetRecovery ∧ ¬ offsetRecovery ≤ crossSectionRecovery := by
  change ¬ prerequisites crossSectionRecovery ⊆ prerequisites offsetRecovery ∧
    ¬ prerequisites offsetRecovery ⊆ prerequisites crossSectionRecovery
  decide

end ProofDependency

noncomputable section

structure Coirradiation where
  flux : ℝ
  targetAtoms : ℝ
  referenceAtoms : ℝ
  referenceCrossSection : ℝ
  targetResponse : ℝ
  referenceResponse : ℝ
  flux_pos : 0 < flux
  target_atoms_pos : 0 < targetAtoms
  reference_atoms_pos : 0 < referenceAtoms
  reference_cross_section_pos : 0 < referenceCrossSection
  target_response_pos : 0 < targetResponse
  reference_response_pos : 0 < referenceResponse

def referenceActivity (irradiation : Coirradiation) : ℝ :=
  activation irradiation.flux irradiation.referenceAtoms irradiation.referenceCrossSection
    irradiation.referenceResponse

def targetActivity (irradiation : Coirradiation) (crossSection : ℝ) : ℝ :=
  activation irradiation.flux irradiation.targetAtoms crossSection irradiation.targetResponse

theorem reference_activity_pos (irradiation : Coirradiation) :
    0 < referenceActivity irradiation :=
  activation_pos _ _ _ _ irradiation.flux_pos irradiation.reference_atoms_pos
    irradiation.reference_cross_section_pos irradiation.reference_response_pos

structure Observation (irradiation : Coirradiation) (crossSection : ℝ)
    (calibration : CascadeCalibration) where
  coincidence : ℝ
  firstSlope : ℝ
  secondSlope : ℝ
  targetRawRate : ℝ
  targetLoss : ℝ
  targetYield : ℝ
  relativeEfficiency : ℝ
  target_yield_pos : 0 < targetYield
  relative_efficiency_pos : 0 < relativeEfficiency
  coincidence_model : coincidence = microscopicCoincidence (referenceActivity irradiation)
    calibration.jointYield calibration.firstEfficiency calibration.secondEfficiency calibration.angularFactor
  first_ray : firstSlope * Real.sqrt coincidence =
    referenceActivity irradiation * calibration.firstYield * calibration.firstEfficiency
  second_ray : secondSlope * Real.sqrt coincidence =
    referenceActivity irradiation * calibration.secondYield * calibration.secondEfficiency
  target_loss_model : targetRawRate =
    targetActivity irradiation crossSection * targetYield * (relativeEfficiency * calibration.firstEfficiency) -
      targetLoss * coincidence

namespace Observation

variable {irradiation : Coirradiation} {crossSection : ℝ} {calibration : CascadeCalibration}

def backingEstimate (observation : Observation irradiation crossSection calibration) : ℝ :=
  activityFromSlope (observation.firstSlope * observation.secondSlope) calibration

def targetEstimate (observation : Observation irradiation crossSection calibration) : ℝ :=
  transferredActivity
    (restoredRate observation.targetRawRate observation.targetLoss observation.coincidence)
    (restoredMarginal observation.firstSlope (Real.sqrt observation.coincidence))
    observation.targetYield calibration.firstYield observation.relativeEfficiency observation.backingEstimate

def crossSectionEstimate (observation : Observation irradiation crossSection calibration) : ℝ :=
  crossSectionFromRatio irradiation.referenceCrossSection
    (observation.targetEstimate / observation.backingEstimate)
    irradiation.targetAtoms irradiation.referenceAtoms irradiation.targetResponse irradiation.referenceResponse

theorem coincidence_pos (observation : Observation irradiation crossSection calibration) :
    0 < observation.coincidence := by
  rw [observation.coincidence_model]
  unfold microscopicCoincidence
  exact mul_pos (mul_pos (mul_pos (mul_pos (reference_activity_pos irradiation)
    calibration.joint_yield_pos) calibration.first_efficiency_pos)
    calibration.second_efficiency_pos) calibration.angular_pos

theorem backing_estimate_exact (observation : Observation irradiation crossSection calibration) :
    observation.backingEstimate = referenceActivity irradiation := by
  apply cascade_activity_from_linear_rays _ _ _ _ calibration
    (ne_of_gt (reference_activity_pos irradiation))
  · rw [Real.sq_sqrt observation.coincidence_pos.le, observation.coincidence_model]
  · exact observation.first_ray
  · exact observation.second_ray

theorem target_estimate_exact (observation : Observation irradiation crossSection calibration) :
    observation.targetEstimate = targetActivity irradiation crossSection := by
  unfold targetEstimate
  rw [observation.backing_estimate_exact,
    restored_rate_of_loss_model _ _ _ _ observation.target_loss_model]
  simp only [restoredMarginal]
  rw [observation.first_ray]
  exact transferred_activity_exact _ _ _ _ _ _
    (ne_of_gt (reference_activity_pos irradiation)) (ne_of_gt observation.target_yield_pos)
    (ne_of_gt calibration.first_yield_pos) (ne_of_gt calibration.first_efficiency_pos)
    (ne_of_gt observation.relative_efficiency_pos)

theorem cross_section_estimate_exact (observation : Observation irradiation crossSection calibration) :
    observation.crossSectionEstimate = crossSection := by
  unfold crossSectionEstimate
  rw [observation.target_estimate_exact, observation.backing_estimate_exact]
  exact cross_section_from_activation_ratio _ _ _ _ _ _ _
    (ne_of_gt irradiation.flux_pos) (ne_of_gt irradiation.target_atoms_pos)
    (ne_of_gt irradiation.reference_atoms_pos) (ne_of_gt irradiation.reference_cross_section_pos)
    (ne_of_gt irradiation.target_response_pos) (ne_of_gt irradiation.reference_response_pos)

theorem cross_section_eq_rate_ratio
    (observation : Observation irradiation crossSection calibration) :
    observation.crossSectionEstimate =
      crossSectionFromRatio irradiation.referenceCrossSection
        (activityRatioFromRates
          (restoredRate observation.targetRawRate observation.targetLoss observation.coincidence)
          (restoredMarginal observation.firstSlope (Real.sqrt observation.coincidence))
          observation.targetYield calibration.firstYield observation.relativeEfficiency)
        irradiation.targetAtoms irradiation.referenceAtoms
        irradiation.targetResponse irradiation.referenceResponse := by
  have backing_ne : observation.backingEstimate ≠ 0 := by
    rw [observation.backing_estimate_exact]
    exact ne_of_gt (reference_activity_pos irradiation)
  simp only [crossSectionEstimate, targetEstimate, transferredActivity,
    mul_div_cancel_left₀ _ backing_ne]

theorem measurement_chain
    (observation : Observation irradiation crossSection calibration)
    (slope measuredIntercept virtualDepth offset : ℝ) (slope_ne : slope ≠ 0)
    (intercept_law : measuredIntercept = fittedIntercept slope virtualDepth offset) :
    observation.backingEstimate = referenceActivity irradiation ∧
    observation.targetEstimate = targetActivity irradiation crossSection ∧
    observation.crossSectionEstimate = crossSection ∧
    offsetFromFit slope measuredIntercept virtualDepth = offset := by
  refine ⟨observation.backing_estimate_exact, observation.target_estimate_exact,
    observation.cross_section_estimate_exact, ?_⟩
  rw [intercept_law]
  exact offset_from_fit_exact slope virtualDepth offset slope_ne

end Observation

end

end InfoGeometry.NuclearReactions.StackedFoilInSitu
