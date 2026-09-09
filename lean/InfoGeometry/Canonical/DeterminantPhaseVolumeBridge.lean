import InfoGeometry.OperatorAlgebra.OperatorThermodynamics
import InfoGeometry.Meta.Architecture

noncomputable section

/-!
# InfoGeometry.Canonical.DeterminantPhaseVolumeBridge

Theorem-safe determinant/phase-volume and RG fixed-point sockets.

This file deliberately does not model determinant as a ring homomorphism out of
operators.  Determinant/phase-volume data is a calibrated readout channel, and
flow invariance is supplied as an explicit law.  Renormalization fixed-point
invariance is kept as a separate theorem surface.
-/

namespace InfoGeometry.Canonical.DeterminantPhaseVolumeBridge

open InfoGeometry.OperatorAlgebra.Thermodynamics

/--
A determinant/phase-volume readout channel.

This is deliberately not a ring homomorphism.  Determinants are multiplicative,
not additive, and in Type-III settings such readouts require a calibration
backend: centralizer, core, regularized determinant, zeta determinant, or a
model-specific replacement.
-/
@[rep_depth operator]
structure DeterminantPhaseVolumeCarrier
    (Op Volume : Type*) where
  /-- Calibrated determinant/phase-volume readout. -/
  detReadout : Op → Volume

/--
A determinant phase-volume system with a modular/automorphism-like flow.
-/
@[rep_depth operator]
structure FlowDeterminantVolumeCarrier
    (Op Volume : Type*) [Ring Op] where
  /-- Ring-level modular/automorphism-like flow. -/
  flow : ModularFlow Op

  /-- Calibrated determinant/phase-volume readout. -/
  det : DeterminantPhaseVolumeCarrier Op Volume

/--
External predicate: the flow preserves the determinant/phase-volume readout.

This is a calibration law, not automatic from Type-III structure.
-/
@[rep_depth thermo]
def FlowPreservesDeterminant
    {Op Volume : Type*} [Ring Op]
    (B : FlowDeterminantVolumeCarrier Op Volume) : Prop :=
  ∀ (t : ℝ) (A : Op),
    B.det.detReadout (B.flow.flow t A) = B.det.detReadout A

namespace FlowDeterminantVolumeCarrier

variable {Op Volume : Type*} [Ring Op]
variable (B : FlowDeterminantVolumeCarrier Op Volume)

/--
Readback theorem: if the determinant channel is calibrated as flow-invariant,
then modular time preserves phase volume.
-/
@[rep_depth thermo]
theorem flow_phase_volume_invariant
    (hDet : FlowPreservesDeterminant B)
    (A : Op) (t : ℝ) :
    B.det.detReadout (B.flow.flow t A) = B.det.detReadout A :=
  hDet t A

end FlowDeterminantVolumeCarrier

/-! ## Renormalization fixed-point readout -/

/--
Carrier for a renormalization map.

No ergodic theorem or determinant theorem is asserted here.
-/
@[rep_depth projective]
structure RenormalizationCarrier
    (Op : Type*) where
  /-- Supplied renormalization/self-similarity map. -/
  renorm : Op → Op

/-- External predicate: `A` is a self-similar fixed point of the renormalization map. -/
@[rep_depth projective]
def IsSelfSimilarFixedPoint
    {Op : Type*}
    (R : RenormalizationCarrier Op)
    (A : Op) : Prop :=
  R.renorm A = A

/--
A volume-density readout over a renormalization system.
-/
@[rep_depth projective]
structure RenormalizedVolumeDensityCarrier
    (Op Volume : Type*) where
  /-- Supplied renormalization map. -/
  renormCarrier : RenormalizationCarrier Op

  /-- Volume-density/readout channel. -/
  volumeDensity : Op → Volume

namespace RenormalizedVolumeDensityCarrier

variable {Op Volume : Type*}
variable (B : RenormalizedVolumeDensityCarrier Op Volume)

/--
At a fixed point, renormalization leaves any readout unchanged by definitional
rewriting.  No determinant theorem is needed here.
-/
@[rep_depth projective]
theorem volume_density_fixed_point_readback
    (A : Op)
    (hA : IsSelfSimilarFixedPoint B.renormCarrier A) :
    B.volumeDensity (B.renormCarrier.renorm A) = B.volumeDensity A := by
  rw [hA]

end RenormalizedVolumeDensityCarrier

end InfoGeometry.Canonical.DeterminantPhaseVolumeBridge
