import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

namespace InfoGeometry.NuclearReactions.ActivationKinetics

noncomputable section

def saturation (decayConstant irradiationTime : ℝ) : ℝ :=
  1 - Real.exp (-decayConstant * irradiationTime)

def decayResponse (decayConstant irradiationTime coolingTime : ℝ) : ℝ :=
  saturation decayConstant irradiationTime * Real.exp (-decayConstant * coolingTime)

def inventory (productionRate decayConstant elapsed : ℝ) : ℝ :=
  productionRate / decayConstant * saturation decayConstant elapsed

def activation (flux atomCount crossSection response : ℝ) : ℝ :=
  flux * atomCount * crossSection * response

def constantFluxActivity
    (flux atomCount crossSection decayConstant irradiationTime coolingTime : ℝ) : ℝ :=
  activation flux atomCount crossSection (decayResponse decayConstant irradiationTime coolingTime)

def constantFluenceActivity
    (fluence atomCount crossSection decayConstant irradiationTime coolingTime : ℝ) : ℝ :=
  constantFluxActivity (fluence / irradiationTime) atomCount crossSection
    decayConstant irradiationTime coolingTime

theorem saturation_pos (decayConstant irradiationTime : ℝ)
    (decay_pos : 0 < decayConstant) (time_pos : 0 < irradiationTime) :
    0 < saturation decayConstant irradiationTime := by
  unfold saturation
  apply sub_pos.mpr
  rw [Real.exp_lt_one_iff]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos decay_pos) time_pos

theorem decay_response_pos (decayConstant irradiationTime coolingTime : ℝ)
    (decay_pos : 0 < decayConstant) (time_pos : 0 < irradiationTime) :
    0 < decayResponse decayConstant irradiationTime coolingTime :=
  mul_pos (saturation_pos decayConstant irradiationTime decay_pos time_pos) (Real.exp_pos _)

theorem inventory_initial (productionRate decayConstant : ℝ) :
    inventory productionRate decayConstant 0 = 0 := by
  simp [inventory, saturation]

theorem hasDerivAt_inventory (productionRate decayConstant elapsed : ℝ)
    (decay_ne : decayConstant ≠ 0) :
    HasDerivAt (inventory productionRate decayConstant)
      (productionRate - decayConstant * inventory productionRate decayConstant elapsed) elapsed := by
  have exponential := (((hasDerivAt_id elapsed).const_mul (-decayConstant)).exp).const_sub 1
  convert exponential.const_mul (productionRate / decayConstant) using 1
  unfold inventory saturation
  simp only [id_eq]
  field_simp [decay_ne]
  ring

theorem cooled_inventory_activity
    (flux atomCount crossSection decayConstant irradiationTime coolingTime : ℝ)
    (decay_ne : decayConstant ≠ 0) :
    decayConstant * inventory (flux * atomCount * crossSection) decayConstant irradiationTime *
        Real.exp (-decayConstant * coolingTime) =
      constantFluxActivity flux atomCount crossSection decayConstant irradiationTime coolingTime := by
  unfold inventory constantFluxActivity activation decayResponse
  field_simp [decay_ne]

theorem fluence_activity_eq_flux_activity
    (flux atomCount crossSection decayConstant irradiationTime coolingTime : ℝ)
    (time_ne : irradiationTime ≠ 0) :
    constantFluenceActivity (flux * irradiationTime) atomCount crossSection
        decayConstant irradiationTime coolingTime =
      constantFluxActivity flux atomCount crossSection decayConstant irradiationTime coolingTime := by
  simp [constantFluenceActivity, time_ne]

theorem activation_pos (flux atomCount crossSection response : ℝ)
    (flux_pos : 0 < flux) (atoms_pos : 0 < atomCount)
    (cross_section_pos : 0 < crossSection) (response_pos : 0 < response) :
    0 < activation flux atomCount crossSection response := by
  unfold activation
  positivity

theorem common_flux_cancellation
    (flux targetAtoms referenceAtoms targetCrossSection referenceCrossSection
      targetResponse referenceResponse : ℝ) (flux_ne : flux ≠ 0) :
    activation flux targetAtoms targetCrossSection targetResponse /
        activation flux referenceAtoms referenceCrossSection referenceResponse =
      (targetAtoms * targetCrossSection * targetResponse) /
        (referenceAtoms * referenceCrossSection * referenceResponse) := by
  simp only [activation, mul_assoc]
  exact mul_div_mul_left _ _ flux_ne

theorem common_area_flux_cancellation
    (flux area targetArealDensity referenceArealDensity targetCrossSection referenceCrossSection
      targetResponse referenceResponse : ℝ) (flux_ne : flux ≠ 0) (area_ne : area ≠ 0) :
    activation flux (area * targetArealDensity) targetCrossSection targetResponse /
        activation flux (area * referenceArealDensity) referenceCrossSection referenceResponse =
      (targetArealDensity * targetCrossSection * targetResponse) /
        (referenceArealDensity * referenceCrossSection * referenceResponse) := by
  have area_factor (density crossSection response : ℝ) :
      activation flux (area * density) crossSection response =
        activation (flux * area) density crossSection response := by
    unfold activation
    ring
  rw [area_factor, area_factor]
  exact common_flux_cancellation _ _ _ _ _ _ _ (mul_ne_zero flux_ne area_ne)

def crossSectionFromRatio
    (referenceCrossSection activityRatio targetAtoms referenceAtoms targetResponse referenceResponse : ℝ) : ℝ :=
  referenceCrossSection * activityRatio * (referenceAtoms * referenceResponse) /
    (targetAtoms * targetResponse)

theorem cross_section_from_activation_ratio
    (flux targetAtoms referenceAtoms targetCrossSection referenceCrossSection
      targetResponse referenceResponse : ℝ)
    (flux_ne : flux ≠ 0) (target_atoms_ne : targetAtoms ≠ 0)
    (reference_atoms_ne : referenceAtoms ≠ 0) (reference_cross_section_ne : referenceCrossSection ≠ 0)
    (target_response_ne : targetResponse ≠ 0) (reference_response_ne : referenceResponse ≠ 0) :
    crossSectionFromRatio referenceCrossSection
        (activation flux targetAtoms targetCrossSection targetResponse /
          activation flux referenceAtoms referenceCrossSection referenceResponse)
        targetAtoms referenceAtoms targetResponse referenceResponse = targetCrossSection := by
  rw [common_flux_cancellation _ _ _ _ _ _ _ flux_ne]
  unfold crossSectionFromRatio
  field_simp

end

end InfoGeometry.NuclearReactions.ActivationKinetics
