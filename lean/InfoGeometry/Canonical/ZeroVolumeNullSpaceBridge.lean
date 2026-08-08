import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.ModularWeightTrace
import InfoGeometry.Canonical.KreinDrazinBoundarySupport

/-!
# Zero Volume Null Space Bridge

This file recasts the informal "zero volume = modular kernel" slogan in the
repo-native language of type III modular integration and algebraic Drazin
splitting.

The type III side is routed through `TypeIIIIntegrationDatum`:

* there is no bare trace on the base algebra;
* scalar readout is obtained from the crossed-product/core trace;
* the compressed topological volume is read through the regular Drazin support.

The modular-kernel side is the Drazin defect sector `q * x = x`.

The equivalence between the zero-volume null space and the defect sector is
kept theorem-safe by an explicit compatibility property.  The bridge does not
invent a trace on the type III base algebra.
-/

noncomputable section

open scoped ENNReal

namespace InfoGeometry.Canonical.ZeroVolumeNullSpaceBridge

open InfoGeometry.OperatorAlgebra
open InfoGeometry.Canonical.KreinDrazinBoundarySupport

set_option linter.dupNamespace false

section Core

variable {M Core : Type*}
variable [AddCommMonoid M] [Ring M] [Star M] [Mul Core]

/--
The zero-volume null-space bridge.

`integration` carries the type III modular weight/core-trace data, while
`drazin` carries the algebraic regular/defect split.
-/
structure ZeroVolumeNullSpacePacket where
  /-- Type III modular integration data routed through the crossed-product core. -/
  integration : TypeIIIIntegrationDatum M Core

  /-- Algebraic Drazin split of the base observable algebra. -/
  drazin : AlgebraicDrazinSplit M

  /--
  Compatibility property: the compressed topological volume vanishes exactly
  on the Drazin defect sector.
  -/
  volume_vanishes_iff_defect_fixed :
    ∀ x : M,
      integration.coreTraceOfBase (drazin.p * x * drazin.p) = 0 ↔
        drazin.q * x = x

namespace ZeroVolumeNullSpacePacket

variable (B : ZeroVolumeNullSpacePacket (M := M) (Core := Core))

/-- The compressed topological volume readout. -/
def topologicalVolume (x : M) : ℝ≥0∞ :=
  B.integration.coreTraceOfBase (B.drazin.p * x * B.drazin.p)

/-- The zero-volume null space. -/
def zeroVolumeNullSpace : Set M :=
  {x | B.topologicalVolume x = 0}

/-- The modular kernel, i.e. the Drazin singular/defect sector. -/
def modularKernel : Set M :=
  {x | B.drazin.q * x = x}

/-- The regular and defect projectors are orthogonal on both sides. -/
theorem regular_defect_orthogonal :
    B.drazin.p * B.drazin.q = 0 ∧ B.drazin.q * B.drazin.p = 0 :=
  ⟨B.drazin.pq_zero, B.drazin.qp_zero⟩

/-- Readback: zero compressed volume is equivalent to the modular kernel. -/
theorem zero_volume_iff_modularKernel (x : M) :
    x ∈ B.zeroVolumeNullSpace ↔ x ∈ B.modularKernel := by
  simpa [ZeroVolumeNullSpacePacket.zeroVolumeNullSpace,
    ZeroVolumeNullSpacePacket.modularKernel,
    ZeroVolumeNullSpacePacket.topologicalVolume] using
    B.volume_vanishes_iff_defect_fixed x

/--
The zero-volume null space coincides with the Drazin singular sector.

This is the theorem-safe version of the draft statement: the equivalence is
carried by the explicit compatibility property on the packet.
-/
theorem zero_volume_is_singular_sector :
    B.zeroVolumeNullSpace = B.modularKernel := by
  ext x
  exact B.zero_volume_iff_modularKernel x

end ZeroVolumeNullSpacePacket

end Core

end InfoGeometry.Canonical.ZeroVolumeNullSpaceBridge
