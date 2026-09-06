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
  vacuumMode_eq_one_witness :
    split.zeroMode.vacuumMode = 1
  regulatedHeatKernel_eq_subtract_one_witness :
    ∀ t : ℝ,
      split.zeroMode.regulatedHeatKernel t =
        split.zeroMode.heatKernel t - split.zeroMode.vacuumMode
  superKMS_detailed_balance_witness :
    kms.absorption = kms.spontaneousEmission + kms.stimulatedEmission

namespace ProjectiveBoundaryPacket

variable {Q : EndH}

/-- The vacuum mode is normalized to one in the projective boundary packet. -/
theorem vacuumMode_eq_one (B : ProjectiveBoundaryPacket Q) :
    B.split.zeroMode.vacuumMode = 1 :=
  B.vacuumMode_eq_one_witness

/-- The regulated heat kernel is the vacuum-subtracted kernel witness. -/
theorem regulatedHeatKernel_eq_subtract_one (B : ProjectiveBoundaryPacket Q) (t : ℝ) :
    B.split.zeroMode.regulatedHeatKernel t =
      B.split.zeroMode.heatKernel t - B.split.zeroMode.vacuumMode :=
  B.regulatedHeatKernel_eq_subtract_one_witness t

omit [CompleteSpace E] in
/-- The Drazin core is definitionally the kernel of the hopping operator. -/
theorem drazinCore_eq_kernel (Q : EndH) :
    DrazinCore Q = (susyHoppingOperator Q).ker := rfl

omit [CompleteSpace E] in
/-- The excited sector is definitionally the orthogonal complement. -/
theorem excitedStateSector_eq_orthogonal (Q : EndH) :
    ExcitedStateSector Q = (DrazinCore Q)ᗮ := rfl

/-- Einstein-style detailed balance is an explicit KMS witness. -/
theorem superKMS_detailed_balance (B : ProjectiveBoundaryPacket Q) :
    B.kms.absorption = B.kms.spontaneousEmission + B.kms.stimulatedEmission :=
  B.superKMS_detailed_balance_witness

/--
Constructor wrapper for a projective boundary packet.

This is intentionally only a repackaging of supplied data and supplied proofs.
-/
def ofWitnesses
    {Q : EndH}
    (split : DrazinChiralSplitPacket (E := E) Q)
    (kms : SuperKMSEquilibriumState)
    (hVac :
      split.zeroMode.vacuumMode = 1)
    (hReg :
      ∀ t : ℝ,
        split.zeroMode.regulatedHeatKernel t =
          split.zeroMode.heatKernel t - split.zeroMode.vacuumMode)
    (hKMS :
      kms.absorption = kms.spontaneousEmission + kms.stimulatedEmission) :
    ProjectiveBoundaryPacket Q where
  split := split
  kms := kms
  vacuumMode_eq_one_witness := hVac
  regulatedHeatKernel_eq_subtract_one_witness := hReg
  superKMS_detailed_balance_witness := hKMS

/-- The projective boundary packet exposes the zero-mode subtraction and KMS balance together. -/
theorem projective_boundary_packet (B : ProjectiveBoundaryPacket Q) :
    B.split.zeroMode.vacuumMode = 1 ∧
    (∀ t : ℝ,
      B.split.zeroMode.regulatedHeatKernel t =
        B.split.zeroMode.heatKernel t - B.split.zeroMode.vacuumMode) ∧
    B.kms.absorption = B.kms.spontaneousEmission + B.kms.stimulatedEmission :=
  ⟨B.vacuumMode_eq_one,
   B.regulatedHeatKernel_eq_subtract_one B,
   B.superKMS_detailed_balance B⟩

end ProjectiveBoundaryPacket

end Core

end InfoGeometry.Canonical.ProjectiveCCR
