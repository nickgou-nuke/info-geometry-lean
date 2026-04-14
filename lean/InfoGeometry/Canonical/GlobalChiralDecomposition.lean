import InfoGeometry.Canonical.RelativeModularScaleShapeSplit
import InfoGeometry.Canonical.DPDWedgeCompatibility
import InfoGeometry.Canonical.DrazinPenroseDilationKKT
import InfoGeometry.Canonical.DrazinSupercharge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.GlobalChiralDecomposition

open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.RelativeModularScaleShapeSplit
open InfoGeometry.Canonical.DPDWedgeCompatibility
open InfoGeometry.Canonical.DrazinPenroseDilationKKT
open InfoGeometry.Canonical.DrazinSupercharge

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance

/--
Global active/apex decomposition on the doubled-real carrier.
If an operator commutes with the active Drazin projector, mixed blocks vanish and
it splits canonically into apex-supported and active-supported parts.
-/
@[rep_depth transport, capstone]
theorem activeApex_decomposition_of_commute
    (CIK : CertifiedInverseKernel H₂)
    (R : EndH)
    (hComm : Commute CIK.spectralProjector R) :
    R
      =
    IsCompatibleDPDWedge.relativeModularKernelScalePart (CIK := CIK) R
      +
    IsCompatibleDPDWedge.relativeModularActiveShapePart (CIK := CIK) R := by
  rcases mixed_blocks_vanish_of_commute_spectralProjector
      (E := E) (CIK := CIK) (H_gen := R) hComm with
    ⟨hQD_R_PD_zero, hPD_R_QD_zero⟩
  exact IsCompatibleDPDWedge.relativeModular_scaleShapeSplit
    (E := E)
    (CIK := CIK)
    (RMO := R)
    hQD_R_PD_zero
    hPD_R_QD_zero

/--
Projector-compressed form of the global active/apex decomposition.
-/
@[rep_depth transport]
theorem activeApex_decomposition_projector_form_of_commute
    (CIK : CertifiedInverseKernel H₂)
    (R : EndH)
    (hComm : Commute CIK.spectralProjector R) :
    R
      =
    CIK.spectralComplementaryProjector * R * CIK.spectralComplementaryProjector
      +
    CIK.spectralProjector * R * CIK.spectralProjector := by
  simpa [IsCompatibleDPDWedge.relativeModularKernelScalePart,
    IsCompatibleDPDWedge.relativeModularActiveShapePart] using
    activeApex_decomposition_of_commute (E := E) (CIK := CIK) (R := R) hComm

/--
Chiral range/domain decomposition identity on the DPD-KKT lane:
`Γ_G = P_R - P_L`.
-/
@[rep_depth krein]
theorem chiralRangeDomain_decomposition
    (K : DPDKKT H₂) :
    K.GammaG = K.P_R - K.P_L := by
  rfl

/--
Half-gap chiral decomposition identity:
`2G = P_R - P_L`.
-/
@[rep_depth krein]
theorem chiralHalfGap_decomposition
    (K : DPDKKT H₂) :
    (2 : ℝ) • K.G = K.P_R - K.P_L := by
  calc
    (2 : ℝ) • K.G = K.GammaG := K.two_smul_G_eq_GammaG
    _ = K.P_R - K.P_L := chiralRangeDomain_decomposition (E := E) K

/--
Chiral KKT closure law on the half-gap generator.
-/
@[rep_depth krein]
theorem chiralKKT_commutator_halfGap_closure
    (K : DPDKKT H₂) :
    DrazinPenroseDilationKKT.commutator K.P_D K.G
      =
    ((2 : ℝ)⁻¹) • (K.rightSupercharge - K.leftSupercharge) :=
  K.commutator_P_D_G_eq_half_sub_supercharges

/--
Chiral KKT closure law on the geometric Cartan generator.
-/
@[rep_depth krein]
theorem chiralKKT_commutator_geometric_closure
    (K : DPDKKT H₂) :
    DrazinPenroseDilationKKT.commutator K.P_D K.GammaG
      =
    K.rightSupercharge - K.leftSupercharge :=
  K.commutator_P_D_GammaG_eq_rightSupercharge_sub_leftSupercharge

/--
Supergraded closure projection from the KKT lane:
`Q = [P_D, Γ_G]`.
-/
@[rep_depth transport]
theorem supergraded_supercharge_closure
    (CIK : CertifiedInverseKernel H₂) :
    DrazinSupercharge.CertifiedInverseKernel.supercharge CIK
      =
    DrazinSupercharge.commutator CIK.spectralProjector CIK.GammaG :=
  DrazinSupercharge.CertifiedInverseKernel.supercharge_eq_commutator_spectralProjector_GammaG
    (CIK := CIK)

/--
Capstone package: singular replacement for clean global polar/KAN factorization.
It combines:
1) active/apex projector decomposition,
2) chiral range/domain half-gap decomposition,
3) anomaly commutator closure on the singular carrier.
-/
@[rep_depth transport, capstone]
theorem singularPolarKAN_replacement_of_commute
    (CIK : CertifiedInverseKernel H₂)
    (R : EndH)
    (hComm : Commute CIK.spectralProjector R) :
    R
      =
    CIK.spectralComplementaryProjector * R * CIK.spectralComplementaryProjector
      +
    CIK.spectralProjector * R * CIK.spectralProjector
      ∧
    CIK.mpRangeProjector - CIK.metricProjector = (2 : ℝ) • CIK.dilationGap
      ∧
    CIK.spectralProjector * CIK.dilationGap - CIK.dilationGap * CIK.spectralProjector
      =
    ((2 : ℝ)⁻¹) • (CIK.rightChiralAnomaly - CIK.chiralAnomaly) := by
  refine ⟨?_, ?_, ?_⟩
  · exact activeApex_decomposition_projector_form_of_commute
      (E := E) (CIK := CIK) (R := R) hComm
  · exact CIK.mpRangeProjector_sub_metricProjector_eq_two_smul_dilationGap
  · exact CIK.spectralProjector_commutator_dilationGap_eq_half_sub_anomalies

end Core

end InfoGeometry.Canonical.GlobalChiralDecomposition
