import Omega.CircleDimension.KernelRKHSFeatureMap

namespace Omega.TypedAddressBiaxialCompletion

/-- The explicit finite sum for `K_ν` exhibits a finite-rank kernel, the CircleDimension
feature-map wrapper gives the resulting RKHS package, and the boundary scalar `H_ν` is the
diagonal restriction of the same kernel object.
    thm:typed-address-biaxial-completion-comoving-rkhs -/
theorem paper_typed_address_biaxial_completion_comoving_rkhs
    (kernelFeatureMapData : Omega.CircleDimension.KernelRKHSFeatureMapData)
    (explicitKernelFiniteRankSum boundaryScalarProfile finiteRankKernel finiteRankRKHS
      boundaryScalarDiagonalRestriction : Prop)
    (deriveFiniteRankKernel : explicitKernelFiniteRankSum → finiteRankKernel)
    (deriveFiniteRankRKHS :
      finiteRankKernel → kernelFeatureMapData.rkhsCharacterization → finiteRankRKHS)
    (deriveBoundaryScalarDiagonalRestriction :
      boundaryScalarProfile → kernelFeatureMapData.featureMapIdentity →
        kernelFeatureMapData.reproducingProperty → boundaryScalarDiagonalRestriction)
    (hExplicitKernelFiniteRankSum : explicitKernelFiniteRankSum)
    (hBoundaryScalarProfile : boundaryScalarProfile) :
    finiteRankKernel ∧ finiteRankRKHS ∧ boundaryScalarDiagonalRestriction := by
  have hFeatureMap :
      kernelFeatureMapData.featureMapIdentity ∧
        kernelFeatureMapData.rkhsCharacterization ∧
        kernelFeatureMapData.projectionNormCharacterization ∧
        kernelFeatureMapData.reproducingProperty :=
    Omega.CircleDimension.paper_cdim_kernel_rkhs_feature_map kernelFeatureMapData
  rcases hFeatureMap with ⟨hFeatureIdentity, hRKHS, _, hReproducing⟩
  have hFiniteRankKernel : finiteRankKernel :=
    deriveFiniteRankKernel hExplicitKernelFiniteRankSum
  exact ⟨hFiniteRankKernel, deriveFiniteRankRKHS hFiniteRankKernel hRKHS,
    deriveBoundaryScalarDiagonalRestriction
      hBoundaryScalarProfile hFeatureIdentity hReproducing⟩

end Omega.TypedAddressBiaxialCompletion
