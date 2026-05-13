import InfoGeometry.Canonical.WeylHomogeneousReadoutBridge
import InfoGeometry.GromovWittenErlangen.GWProjectiveCountCalibration
import InfoGeometry.OperatorAlgebra.DrazinEntropyFunctional
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.WeylGWVolumeBridge

Canonical fusion layer for projective GW counts, Drazin/GW volume calibration,
and Weyl gauge-fixed physical volume.

This file reuses existing repo owner lanes:

* `GromovWittenErlangen.GWProjectiveCountCalibration` owns the raw
  unnormalized/projective GW count calibration.
* `OperatorAlgebra.DrazinGWVolumeCalibration` owns the Drazin entropy to
  GW-volume readout.
* `Canonical.WeylHomogeneousReadoutBridge` owns the generic Weyl homogeneous
  readout interface.

The only new theorem here is the algebraic Weyl cancellation:

```text
weight 2 intensity × inverse-weight 2 gauge = scale-invariant volume.
```

All physical identifications remain explicit predicates/hypotheses.
-/

namespace InfoGeometry.Canonical.WeylGWVolumeBridge

open InfoGeometry.Canonical.WeylHomogeneousReadoutBridge
open InfoGeometry.GromovWittenErlangen
open InfoGeometry.OperatorAlgebra

/--
Mirror/twin GW intensity carrier.

This names the raw local count, mirror/twin count, and their intensity readout.
The equation `twinIntensity = localCount * mirrorCount` is an external
predicate, not a bundled law.
-/
@[rep_depth projective]
structure MirrorTwinGWCalibration
    (State : Type*) where
  scale : ℝ → State → State
  localCount : State → ℝ
  mirrorCount : State → ℝ
  twinIntensity : State → ℝ

/-- External predicate: twin intensity is the product of a count and its mirror count. -/
@[rep_depth projective]
def IsMirrorTwinIntensity
    {State : Type*}
    (M : MirrorTwinGWCalibration State) : Prop :=
  ∀ s : State, M.twinIntensity s = M.localCount s * M.mirrorCount s

/-- External predicate: the twin intensity has Weyl weight two. -/
@[rep_depth projective]
def IsWeightTwoTwinIntensity
    {State : Type*}
    (M : MirrorTwinGWCalibration State) : Prop :=
  ∀ (c : ℝ) (s : State),
    M.twinIntensity (M.scale c s) = c ^ 2 * M.twinIntensity s

namespace MirrorTwinGWCalibration

variable {State : Type*}
variable (M : MirrorTwinGWCalibration State)

@[rep_depth projective]
theorem localCount_apply (s : State) :
    M.localCount s = M.localCount s := rfl

@[rep_depth projective]
theorem mirrorCount_apply (s : State) :
    M.mirrorCount s = M.mirrorCount s := rfl

@[rep_depth projective]
theorem twinIntensity_apply (s : State) :
    M.twinIntensity s = M.twinIntensity s := rfl

end MirrorTwinGWCalibration

/--
Automorphic/Weyl inverse-scale carrier.

The gauge factor is expected to cancel a declared Weyl weight.  The inverse
weight-two law is external.
-/
@[rep_depth projective]
structure AutomorphicScaleBridge
    (State : Type*) where
  scale : ℝ → State → State
  gaugeScale : State → ℝ

/-- External predicate: the gauge scale has inverse Weyl weight two. -/
@[rep_depth projective]
def IsInverseWeightTwoGauge
    {State : Type*}
    (G : AutomorphicScaleBridge State) : Prop :=
  ∀ (c : ℝ) (s : State),
    c ≠ 0 →
      G.gaugeScale (G.scale c s) = (c ^ 2)⁻¹ * G.gaugeScale s

namespace AutomorphicScaleBridge

variable {State : Type*}
variable (G : AutomorphicScaleBridge State)

@[rep_depth projective]
theorem gaugeScale_apply (s : State) :
    G.gaugeScale s = G.gaugeScale s := rfl

end AutomorphicScaleBridge

/--
Physical Weyl/GW volume carrier.

This carrier keeps a single common Weyl scaling action.  The product law
`physicalVolume = twinIntensity * gaugeScale` is an external predicate.
-/
@[rep_depth projective]
structure WeylGWVolumeCarrier
    (State : Type*) where
  scale : ℝ → State → State
  twinIntensity : State → ℝ
  gaugeScale : State → ℝ
  physicalVolume : State → ℝ

/-- External predicate: the physical volume is intensity times gauge scale. -/
@[rep_depth projective]
def IsGaugeFixedVolume
    {State : Type*}
    (V : WeylGWVolumeCarrier State) : Prop :=
  ∀ s : State, V.physicalVolume s = V.twinIntensity s * V.gaugeScale s

/-- External predicate: the volume carrier's twin intensity has Weyl weight two. -/
@[rep_depth projective]
def HasWeightTwoIntensity
    {State : Type*}
    (V : WeylGWVolumeCarrier State) : Prop :=
  ∀ (c : ℝ) (s : State),
    V.twinIntensity (V.scale c s) = c ^ 2 * V.twinIntensity s

/-- External predicate: the volume carrier's gauge scale has inverse Weyl weight two. -/
@[rep_depth projective]
def HasInverseWeightTwoGauge
    {State : Type*}
    (V : WeylGWVolumeCarrier State) : Prop :=
  ∀ (c : ℝ) (s : State),
    c ≠ 0 →
      V.gaugeScale (V.scale c s) = (c ^ 2)⁻¹ * V.gaugeScale s

namespace WeylGWVolumeCarrier

variable {State : Type*}
variable (V : WeylGWVolumeCarrier State)

@[rep_depth projective]
theorem physicalVolume_apply (s : State) :
    V.physicalVolume s = V.physicalVolume s := rfl

/--
Gauge-fixed physical volume is invariant under nonzero Weyl scaling.

This is the core closure theorem of this file.
-/
@[rep_depth projective]
theorem physicalVolume_weylInvariant
    (hV : IsGaugeFixedVolume V)
    (hI : HasWeightTwoIntensity V)
    (hG : HasInverseWeightTwoGauge V)
    (c : ℝ) (s : State) (hc : c ≠ 0) :
    V.physicalVolume (V.scale c s) = V.physicalVolume s := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  rw [hV (V.scale c s), hI c s, hG c s hc, hV s]
  field_simp [hc2]

end WeylGWVolumeCarrier

/--
Canonical fusion socket connecting projective GW counts, Drazin/GW volume, and
Weyl gauge-fixed physical volume.

This is a carrier.  The equality between the physical volume and the Drazin/GW
volume is an external predicate below.
-/
@[rep_depth projective]
structure ProjectiveDrazinWeylGWVolumeFusion
    (G T Target Coeff Op State : Type*) where
  projectiveCounts : GWProjectiveCountCalibration G T Target Coeff
  drazinGW : DrazinGWVolumeCalibration Op State
  volume : WeylGWVolumeCarrier State

/-- External predicate: physical volume is calibrated to the existing Drazin/GW volume. -/
@[rep_depth projective]
def PhysicalVolumeCalibratesDrazinGW
    {G T Target Coeff Op State : Type*}
    (F : ProjectiveDrazinWeylGWVolumeFusion G T Target Coeff Op State) : Prop :=
  ∀ s : State,
    F.drazinGW.functional.readout.valid s →
      F.volume.physicalVolume s = F.drazinGW.gwVolume s

namespace ProjectiveDrazinWeylGWVolumeFusion

variable {G T Target Coeff Op State : Type*}
variable (F : ProjectiveDrazinWeylGWVolumeFusion G T Target Coeff Op State)

@[rep_depth projective]
theorem projectiveCounts_apply :
    F.projectiveCounts = F.projectiveCounts := rfl

@[rep_depth projective]
theorem drazinGW_apply :
    F.drazinGW = F.drazinGW := rfl

@[rep_depth projective]
theorem volume_apply :
    F.volume = F.volume := rfl

/--
Drazin entropy expressed through the calibrated physical Weyl/GW volume.

This consumes the existing `DrazinGWVolumeCalibration` theorem and the explicit
calibration predicate connecting the physical volume to `gwVolume`.
-/
@[rep_depth projective]
theorem entropy_eq_kB_log_physicalVolume
    (hcal : PhysicalVolumeCalibratesDrazinGW F)
    (s : State) (hs : F.drazinGW.functional.readout.valid s) :
    F.drazinGW.functional.entropy s =
      F.drazinGW.functional.kB * Real.log (F.volume.physicalVolume s) := by
  calc
    F.drazinGW.functional.entropy s
        = F.drazinGW.functional.kB * Real.log (F.drazinGW.gwVolume s) :=
            F.drazinGW.entropy_eq_kB_log_gwVolume s hs
    _ = F.drazinGW.functional.kB * Real.log (F.volume.physicalVolume s) := by
            rw [hcal s hs]

end ProjectiveDrazinWeylGWVolumeFusion

end InfoGeometry.Canonical.WeylGWVolumeBridge
