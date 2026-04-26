import InfoGeometry.Canonical.ChiralNullSpaceBridge
import InfoGeometry.Canonical.SuperKMS_Equilibrium

/-!
# Projective CCR

Owner-facing packet for the projective boundary interpretation:

- the regulated heat kernel subtracts the vacuum zero-mode;
- the Drazin core is the kernel of the hopping operator;
- the excited sector is the orthogonal complement;
- the chiral cones and super-KMS balance remain explicit witnesses.

This file does not assert an entanglement theorem or a `CL(4,4)` closure theorem.
-/

namespace InfoGeometry.Canonical.ProjectiveCCR

open InfoGeometry.Canonical.ChiralNullSpaceBridge
open InfoGeometry.Canonical.TopologicalGapShadow
open InfoGeometry.Canonical.ChiralRadiationCones
open InfoGeometry.Canonical.SuperKMS_Equilibrium

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => E →L[ℝ] E

/-- Projective boundary packet: chiral null space plus zero-mode subtraction. -/
structure ProjectiveBoundaryPacket (Q : EndH) where
  split : DrazinChiralSplitPacket (E := E) Q
  kms : SuperKMSEquilibriumState

namespace ProjectiveBoundaryPacket

variable {Q : EndH}
variable (B : ProjectiveBoundaryPacket (E := E) Q)

/-- The vacuum mode is normalized to one in the projective boundary packet. -/
theorem vacuumMode_eq_one :
    B.split.zeroMode.vacuumMode = 1 := by
  exact B.split.zeroMode.vacuum_eq_one

/-- The regulated heat kernel is the vacuum-subtracted kernel witness. -/
theorem regulatedHeatKernel_eq_subtract_one (t : ℝ) :
    B.split.zeroMode.regulatedHeatKernel t =
      B.split.zeroMode.heatKernel t - B.split.zeroMode.vacuumMode := by
  exact B.split.zeroMode.regulated_eq_subtract t

omit [CompleteSpace E] in
/-- The Drazin core is definitionally the kernel of the hopping operator. -/
theorem drazinCore_eq_kernel (Q : EndH) :
    DrazinCore Q = (susyHoppingOperator Q).ker := rfl

omit [CompleteSpace E] in
/-- The excited sector is definitionally the orthogonal complement. -/
theorem excitedStateSector_eq_orthogonal (Q : EndH) :
    ExcitedStateSector Q = (DrazinCore Q)ᗮ := rfl

/-- Einstein-style detailed balance is an explicit KMS witness. -/
theorem superKMS_detailed_balance :
    B.kms.absorption = B.kms.spontaneousEmission + B.kms.stimulatedEmission := by
  exact B.kms.detailedBalance

/-- The projective boundary packet exposes the zero-mode subtraction and KMS balance together. -/
theorem projective_boundary_packet :
    B.split.zeroMode.vacuumMode = 1 ∧
    (∀ t : ℝ,
      B.split.zeroMode.regulatedHeatKernel t =
        B.split.zeroMode.heatKernel t - B.split.zeroMode.vacuumMode) ∧
    B.kms.absorption = B.kms.spontaneousEmission + B.kms.stimulatedEmission :=
  ⟨B.vacuumMode_eq_one, B.regulatedHeatKernel_eq_subtract_one, B.superKMS_detailed_balance⟩

end ProjectiveBoundaryPacket

end Core

end InfoGeometry.Canonical.ProjectiveCCR
