import InfoGeometry.Canonical.StandardFormOmegaVolumeBridge
import InfoGeometry.Canonical.StandardFormProjectiveGWBridge
import InfoGeometry.Canonical.DeterminantPhaseVolumeBridge
import InfoGeometry.Canonical.WeylHomogeneousReadoutBridge
import InfoGeometry.GromovWittenErlangen.GWProjectiveCountCalibration
import InfoGeometry.OperatorAlgebra.DrazinEntropyFunctional
import InfoGeometry.Meta.Architecture

open scoped BigOperators

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

open InfoGeometry.Canonical.DeterminantPhaseVolumeBridge
open InfoGeometry.Canonical.WeylHomogeneousReadoutBridge
open InfoGeometry.Canonical.StandardFormOmegaVolumeBridge
open InfoGeometry.Canonical.StandardFormProjectiveGWBridge
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
    (G T Target Coeff Op State : Type*) [Add Op] [Mul Op] where
  projectiveCounts : GWProjectiveCountCalibration G T Target Coeff
  drazinGW : DrazinGWVolumeCalibration Op State
  volume : WeylGWVolumeCarrier State

/-- External predicate: physical volume is calibrated to the existing Drazin/GW volume. -/
@[rep_depth projective]
def PhysicalVolumeCalibratesDrazinGW
    {G T Target Coeff Op State : Type*} [Add Op] [Mul Op]
    (F : ProjectiveDrazinWeylGWVolumeFusion G T Target Coeff Op State) : Prop :=
  ∀ s : State,
    F.drazinGW.functional.readout.valid s →
      F.volume.physicalVolume s = F.drazinGW.gwVolume s

namespace ProjectiveDrazinWeylGWVolumeFusion

variable {G T Target Coeff Op State : Type*} [Add Op] [Mul Op]
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

/-! ## Determinant/RG/Weyl readout fusion -/

/--
Fusion socket for the three separate volume-readout mechanisms:

* determinant-like phase volume under modular/ring flow,
* renormalization fixed-point volume density,
* Weyl/projective physical-readout factorization.

This structure deliberately does not assert that a Type-III determinant exists.
The determinant-like readout and its flow invariance are supplied by
`DeterminantPhaseVolumeBridge`.
-/
@[rep_depth projective]
structure PhaseVolumeRGWeylGWVolumeFusion
    (Op Shape Volume : Type*) [Ring Op] where
  /-- Calibrated determinant-like phase-volume carrier. -/
  phaseVolume :
    FlowDeterminantVolumeCarrier Op Volume

  /-- Renormalized volume-density carrier. -/
  renormVolume :
    RenormalizedVolumeDensityCarrier Op ℝ

  /-- Existing Weyl/projective readout factorization owner. -/
  factorization :
    WeylPhysicalReadoutFactorization Op Shape

  /-- Calibration between the RG volume density and Weyl physical readout. -/
  volumeDensity_eq_physicalReadout :
    ∀ A : Op,
      renormVolume.volumeDensity A = factorization.physicalReadout A

namespace PhaseVolumeRGWeylGWVolumeFusion

variable {Op Shape Volume : Type*} [Ring Op]
variable (F : PhaseVolumeRGWeylGWVolumeFusion Op Shape Volume)

/--
Flow preserves determinant-like phase volume when the determinant channel is
explicitly calibrated as flow-invariant.
-/
@[rep_depth thermo]
theorem flow_phase_volume_invariant
    (hDet : FlowPreservesDeterminant F.phaseVolume)
    (A : Op) (t : ℝ) :
    F.phaseVolume.det.detReadout (F.phaseVolume.flow.flow t A) =
      F.phaseVolume.det.detReadout A :=
  FlowDeterminantVolumeCarrier.flow_phase_volume_invariant F.phaseVolume hDet A t

/--
Renormalization leaves volume density unchanged at a supplied self-similar fixed
point.
-/
@[rep_depth projective]
theorem volume_density_fixed_point_readback
    (A : Op)
    (hA : IsSelfSimilarFixedPoint F.renormVolume.renormCarrier A) :
    F.renormVolume.volumeDensity (F.renormVolume.renormCarrier.renorm A) =
      F.renormVolume.volumeDensity A :=
  RenormalizedVolumeDensityCarrier.volume_density_fixed_point_readback F.renormVolume A hA

/--
The physical volume density factors through the Weyl scale and projective shape
core owned by `WeylHomogeneousReadoutBridge`.
-/
@[rep_depth projective]
theorem volumeDensity_eq_weyl_scale_pow_mul_shape
    (A : Op) :
    F.renormVolume.volumeDensity A =
      F.factorization.scaleFactor A ^ F.factorization.weight *
        F.factorization.shapeReadout (F.factorization.shape A) := by
  rw [F.volumeDensity_eq_physicalReadout A]
  exact F.factorization.physical_eq_scale_pow_mul_shape A

end PhaseVolumeRGWeylGWVolumeFusion

/-! ## Standard-form face volume fusion -/

section StandardFormFaces

variable {H Functional State G T Target Coeff Word : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [InfoGeometry.Krein.KreinSpace (InfoGeometry.Krein.DoubledSpace H)]
variable [Fintype Word] [DecidableEq Word]

/--
Fusion socket from standard-form natural-cone face volume to the projective
Weyl/GW physical-volume readout.

The Ω-volume owner supplies finite localized expectations on cone faces.  The
projective GW bridge supplies the gauge-fixed physical volume.  This structure
only records the calibration between those two readouts; it does not claim a
trace, determinant, or canonical Type-III volume.
-/
@[rep_depth projective]
structure StandardFormFaceWeylGWVolumeFusion where
  /-- Projective GW/Weyl bridge enriched with binary-word cone-face localization. -/
  projectiveFace :
    InfoGeometry.Canonical.StandardFormProjectiveGWBridge.FaceBridge
      (H := H) (Functional := Functional)
      (State := State) (G := G) (T := T) (Target := Target) (Coeff := Coeff)

  /-- Ω-expectation finite atom/face volume owner. -/
  omegaVolume :
    NaturalConeVolumeBridge (H := H) Word

  /-- Model-state representative associated to a finite atom/face. -/
  wordToState :
    Word → State

  /--
  Calibration: projective physical volume on a word-state is the Ω-localized
  expectation of that face.
  -/
  localizedVolume_calibration :
    ∀ w : Word,
      projectiveFace.base.physicalVolume (wordToState w) =
        NaturalConeVolumeBridge.localizedExpectation omegaVolume w

namespace StandardFormFaceWeylGWVolumeFusion

variable (F : StandardFormFaceWeylGWVolumeFusion
  (H := H) (Functional := Functional) (State := State)
  (G := G) (T := T) (Target := Target) (Coeff := Coeff) (Word := Word))

/-- Readback: a calibrated word-state physical volume is its Ω-localized face expectation. -/
@[rep_depth projective]
theorem physicalVolume_eq_localizedExpectation
    (w : Word) :
    F.projectiveFace.base.physicalVolume (F.wordToState w) =
      NaturalConeVolumeBridge.localizedExpectation F.omegaVolume w :=
  F.localizedVolume_calibration w

/--
If the localized face operators form a partition of unity, the calibrated
projective physical volumes over the finite word layer sum to one.
-/
@[rep_depth projective]
theorem total_projective_face_volume_is_unity
    (hLocalPartition :
      (∑ w : Word, NaturalConeVolumeBridge.localizationOp F.omegaVolume w) =
        (1 : InfoGeometry.Volume.ConnesCocycle.AlgebraEnd H)) :
    (∑ w : Word, F.projectiveFace.base.physicalVolume (F.wordToState w)) = 1 := by
  calc
    (∑ w : Word, F.projectiveFace.base.physicalVolume (F.wordToState w))
        = ∑ w : Word, NaturalConeVolumeBridge.localizedExpectation F.omegaVolume w := by
            exact Finset.sum_congr rfl
              (fun w _ => F.localizedVolume_calibration w)
    _ = 1 :=
        NaturalConeVolumeBridge.total_localizedExpectation_is_unity
          F.omegaVolume hLocalPartition

/-- The base projective GW/Weyl physical-volume readout remains scale invariant. -/
@[rep_depth projective]
theorem physicalVolume_scale_invariant
    (c : ℝ) (hc : c ≠ 0) (s : State) :
    F.projectiveFace.base.physicalVolume (F.projectiveFace.base.scaleState c s) =
      F.projectiveFace.base.physicalVolume s :=
  StandardFormProjectiveGWBridge.FaceBridge.physicalVolume_scale_invariant
    F.projectiveFace c hc s

end StandardFormFaceWeylGWVolumeFusion

end StandardFormFaces

end InfoGeometry.Canonical.WeylGWVolumeBridge
