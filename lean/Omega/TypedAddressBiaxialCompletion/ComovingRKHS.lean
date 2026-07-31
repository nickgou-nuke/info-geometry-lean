import Omega.CircleDimension.KernelRKHSFeatureMap

namespace Omega.TypedAddressBiaxialCompletion

/-- The explicit finite sum for `K_ν` exhibits a finite-rank kernel, the CircleDimension
feature-map wrapper gives the resulting RKHS package, and the boundary scalar `H_ν` is the
diagonal restriction of the same kernel object.
    thm:typed-address-biaxial-completion-comoving-rkhs -/
theorem paper_typed_address_biaxial_completion_comoving_rkhs
    (spectralKernelFormula featureMapDefined featureMapIdentity rkhsCharacterization
      projectionNormCharacterization reproducingProperty : Prop)
    (spectralKernelFormula_h : spectralKernelFormula)
    (defineFeatureMap : spectralKernelFormula → featureMapDefined)
    (deriveFeatureMapIdentity : featureMapDefined → featureMapIdentity)
    (deriveRkhsCharacterization : featureMapDefined → rkhsCharacterization)
    (deriveProjectionNormCharacterization :
      featureMapDefined → projectionNormCharacterization)
    (deriveReproducingProperty : featureMapDefined → reproducingProperty)
    (explicitKernelFiniteRankSum boundaryScalarProfile finiteRankKernel finiteRankRKHS
      boundaryScalarDiagonalRestriction : Prop)
    (deriveFiniteRankKernel : explicitKernelFiniteRankSum → finiteRankKernel)
    (deriveFiniteRankRKHS : finiteRankKernel → rkhsCharacterization → finiteRankRKHS)
    (deriveBoundaryScalarDiagonalRestriction :
      boundaryScalarProfile → featureMapIdentity → reproducingProperty →
        boundaryScalarDiagonalRestriction)
    (hExplicitKernelFiniteRankSum : explicitKernelFiniteRankSum)
    (hBoundaryScalarProfile : boundaryScalarProfile) :
    finiteRankKernel ∧ finiteRankRKHS ∧ boundaryScalarDiagonalRestriction := by
  have hFeatureMap :
      featureMapIdentity ∧ rkhsCharacterization ∧ projectionNormCharacterization ∧
        reproducingProperty :=
    Omega.CircleDimension.paper_cdim_kernel_rkhs_feature_map
      spectralKernelFormula featureMapDefined featureMapIdentity rkhsCharacterization
      projectionNormCharacterization reproducingProperty spectralKernelFormula_h
      defineFeatureMap deriveFeatureMapIdentity deriveRkhsCharacterization
      deriveProjectionNormCharacterization deriveReproducingProperty
  rcases hFeatureMap with ⟨hFeatureIdentity, hRKHS, _, hReproducing⟩
  have hFiniteRankKernel : finiteRankKernel :=
    deriveFiniteRankKernel hExplicitKernelFiniteRankSum
  exact ⟨hFiniteRankKernel, deriveFiniteRankRKHS hFiniteRankKernel hRKHS,
    deriveBoundaryScalarDiagonalRestriction
      hBoundaryScalarProfile hFeatureIdentity hReproducing⟩

end Omega.TypedAddressBiaxialCompletion
