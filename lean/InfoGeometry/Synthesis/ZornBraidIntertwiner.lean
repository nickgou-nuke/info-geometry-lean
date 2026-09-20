import InfoGeometry.Canonical.CanonicalZornBraidTransport
import InfoGeometry.Canonical.SplitOctonionAutomorphism
import InfoGeometry.Categorical.ZornColimitStageAction

noncomputable section

namespace InfoGeometry.Synthesis.ZornBraidIntertwiner

open CategoryTheory.Limits
open InfoGeometry.Canonical
open InfoGeometry.Canonical.CanonicalZornBraidTransport
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Categorical.ZornUHFColimit
open InfoGeometry.Physics.QCDCanonicalComplexZornBridge (CanonicalZorn canonicalComplexEquiv)
open InfoGeometry.Physics.SplitOctonionBraidSU3 (Q_k)
open InfoGeometry.Physics.YangBaxterZornBridge (LeftMulR)
open InfoGeometry.Physics.B3PresentedGroup (B3)
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3 (zMul)

theorem automorphism_braid_generator_covariance
    (automorphism : ↥(splitOctonionAutSubgroup (R := ℂ)))
    (axis : Fin 3) (state : CanonicalZorn) :
    automorphism.val.conjAlgEquiv ℂ (operatorEquiv (LeftMulR axis)) state =
      state + Complex.I •
        zMul (automorphism.val (canonicalComplexEquiv.symm (Q_k axis))) state := by
  apply braid_generator_covariance
  intro left right
  exact automorphism.property.2 left right

theorem canonical_braid_colimit_intertwines
    (braid : B3) (stage : ℕ) (states : BitWord stage → CanonicalZorn) :
    (zornColimitBraidRepresentation braid : Module.End ℂ ZornColimit)
        ((colimit.ι zornStageFunctor stage).hom (fun word => coordinates (states word))) =
      (colimit.ι zornStageFunctor stage).hom
        (fun word => coordinates
          ((braidRepresentation braid : Module.End ℂ CanonicalZorn) (states word))) := by
  rw [zornColimitBraidRepresentation_on_stage]
  apply congrArg (colimit.ι zornStageFunctor stage).hom
  funext word
  exact (coordinates_intertwines braid (states word)).symm

theorem canonical_inverse_braid_colimit_intertwines
    (braid : B3) (stage : ℕ) (states : BitWord stage → CanonicalZorn) :
    (↑((zornColimitBraidRepresentation braid)⁻¹) : Module.End ℂ ZornColimit)
        ((colimit.ι zornStageFunctor stage).hom (fun word => coordinates (states word))) =
      (colimit.ι zornStageFunctor stage).hom
        (fun word => coordinates
          ((↑((braidRepresentation braid)⁻¹) : Module.End ℂ CanonicalZorn) (states word))) := by
  simpa only [map_inv] using canonical_braid_colimit_intertwines braid⁻¹ stage states

end InfoGeometry.Synthesis.ZornBraidIntertwiner
