import InfoGeometry.Canonical.ChiralNullSpaceBridge
import InfoGeometry.Canonical.SuperKMS_Equilibrium

namespace InfoGeometry.Canonical.ProjectiveCCR

open InfoGeometry.Canonical.ChiralNullSpaceBridge
open InfoGeometry.Canonical.TopologicalGapShadow
open InfoGeometry.Canonical.ChiralRadiationCones
open InfoGeometry.Canonical.SuperKMS_Equilibrium

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => E →L[ℝ] E

structure ProjectiveBoundaryPacket (Q : EndH) where
  split : DrazinChiralSplitPacket (E := E) Q
  kms : SuperKMSEquilibriumState

namespace ProjectiveBoundaryPacket

variable {Q : EndH}

/-- The vacuum mode is normalized to one in the projective boundary packet. -/
theorem vacuumMode_eq_one (B : ProjectiveBoundaryPacket Q) :
    B.split.zeroMode.vacuumMode = 1 :=
  B.split.zeroMode.vacuum_eq_one

/-- The regulated heat kernel is the vacuum-subtracted kernel. -/
theorem regulatedHeatKernel_eq_subtract_one (B : ProjectiveBoundaryPacket Q) (t : ℝ) :
    B.split.zeroMode.regulatedHeatKernel t =
      B.split.zeroMode.heatKernel t - B.split.zeroMode.vacuumMode :=
  B.split.zeroMode.regulated_eq_subtract t

omit [CompleteSpace E] in
/-- The Drazin core is definitionally the kernel of the hopping operator. -/
theorem drazinCore_eq_kernel (Q : EndH) :
    DrazinCore Q = (susyHoppingOperator Q).ker := rfl

omit [CompleteSpace E] in
/-- The excited sector is definitionally the orthogonal complement. -/
theorem excitedStateSector_eq_orthogonal (Q : EndH) :
    ExcitedStateSector Q = (DrazinCore Q)ᗮ := rfl

/-- Einstein-style detailed balance from the KMS equilibrium state. -/
theorem superKMS_detailed_balance (B : ProjectiveBoundaryPacket Q) :
    B.kms.absorption = B.kms.spontaneousEmission + B.kms.stimulatedEmission :=
  B.kms.detailedBalance

end ProjectiveBoundaryPacket

end Core

end InfoGeometry.Canonical.ProjectiveCCR
