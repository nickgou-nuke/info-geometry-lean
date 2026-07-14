import InfoGeometry.Canonical.GlobalChiralDecomposition
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.Sandbox_CP003_SingularPolarDecomposition

CP-003 witness sandbox.

This file is intentionally non-authority and reuses canonical owners from
`GlobalChiralDecomposition`. It exists to preserve translation-facing theorem
names for the singular KAN/polar surrogate claim packet.
-/

namespace Sandbox_CP003_SingularPolarDecomposition

open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.GlobalChiralDecomposition
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
CP-003 witness alias:
global active/apex decomposition on the doubled carrier.
-/
@[rep_depth transport]
theorem global_active_apex_decomposition
    (CIK : CertifiedInverseKernel H₂)
    (R : EndH)
    (hComm : Commute CIK.spectralProjector R) :
    R
      =
    CIK.spectralComplementaryProjector * R * CIK.spectralComplementaryProjector
      +
    CIK.spectralProjector * R * CIK.spectralProjector := by
  exact activeApex_decomposition_projector_form_of_commute
    (E := E) (CIK := CIK) (R := R) hComm

/--
CP-003 witness alias:
chiral range/domain decomposition identity.
-/
@[rep_depth krein]
theorem chiral_range_domain_decomposition
    (K : DPDKKT H₂) :
    K.GammaG = K.P_R - K.P_L := by
  exact chiralRangeDomain_decomposition (E := E) K

/--
CP-003 witness alias:
singular surrogate closure on the geometric Cartan lane.
-/
@[rep_depth krein]
theorem singular_polar_surrogate_closure
    (K : DPDKKT H₂) :
    DrazinPenroseDilationKKT.commutator K.P_D K.GammaG
      =
    K.rightSupercharge - K.leftSupercharge := by
  exact chiralKKT_commutator_geometric_closure (E := E) K

/--
CP-003 witness package:
active/apex decomposition plus KKT closure identities.
-/
@[rep_depth transport, capstone]
theorem cp003_singular_polar_kan_package_of_commute
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
  exact singularPolarKAN_replacement_of_commute
    (E := E) (CIK := CIK) (R := R) hComm

end Core

end Sandbox_CP003_SingularPolarDecomposition
