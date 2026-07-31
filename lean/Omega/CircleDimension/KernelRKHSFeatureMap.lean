import Mathlib.Tactic

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the explicit feature map of the CircleDimension difference kernel.
    prop:cdim-kernel-rkhs-feature-map -/
theorem paper_cdim_kernel_rkhs_feature_map
    (spectralKernelFormula featureMapDefined featureMapIdentity rkhsCharacterization
      projectionNormCharacterization reproducingProperty : Prop)
    (spectralKernelFormula_h : spectralKernelFormula)
    (defineFeatureMap : spectralKernelFormula → featureMapDefined)
    (deriveFeatureMapIdentity : featureMapDefined → featureMapIdentity)
    (deriveRkhsCharacterization : featureMapDefined → rkhsCharacterization)
    (deriveProjectionNormCharacterization :
      featureMapDefined → projectionNormCharacterization)
    (deriveReproducingProperty : featureMapDefined → reproducingProperty) :
    featureMapIdentity ∧ rkhsCharacterization ∧ projectionNormCharacterization ∧
      reproducingProperty := by
  have hFeatureMap : featureMapDefined := defineFeatureMap spectralKernelFormula_h
  exact ⟨deriveFeatureMapIdentity hFeatureMap, deriveRkhsCharacterization hFeatureMap,
    deriveProjectionNormCharacterization hFeatureMap,
    deriveReproducingProperty hFeatureMap⟩

end Omega.CircleDimension
