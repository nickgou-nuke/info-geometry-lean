import InfoGeometry.Arithmetic.ProjectiveWeylGauge
import InfoGeometry.Canonical.ModularCartanCantorSystem
import InfoGeometry.Canonical.StandardFormNaturalConeBridge
import InfoGeometry.GromovWittenErlangen.ProjectiveCountBridge
import InfoGeometry.Meta.Architecture

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.StandardFormProjectiveGWBridge

Calibration-gated projective-shadow bridge.

This file does not assert that Type III data canonically produces GW volume.
It records the theorem-safe composition:

* standard-form normal-cone state geometry;
* projective GW/count shadow data;
* Weyl gauge calibration;
* a weight `+2` GW intensity paired with a weight `-2` inverse Weyl gauge.

The resulting physical-volume readout is scale invariant by cancellation of the
two weights.
-/

noncomputable section

namespace InfoGeometry.Canonical.StandardFormProjectiveGWBridge

open InfoGeometry.Arithmetic.PrimitiveProjectiveRays
open InfoGeometry.Arithmetic.ProjectiveWeylGauge
open InfoGeometry.Canonical.ModularCartanCantorSystem
open InfoGeometry.Canonical.StandardFormNaturalConeBridge
open InfoGeometry.GromovWittenErlangen.ProjectiveCountBridge

section Core

variable {H Functional State G T Target Coeff : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/--
Projective-shadow bridge from standard-form normal-cone data and GW/projective
counts to a gauge-fixed physical volume readout.

All identifications are calibration fields.  In particular, this structure does
not claim that a bare Type III factor determines a GW volume, nor that a Weyl
gauge is canonical.
-/
@[rep_depth projective]
structure StandardFormProjectiveGWBridge where
  /-- Standard-form/natural-cone carrier for normal positive state geometry. -/
  standardCone :
    NaturalConeStandardFormInterface Unit H Functional

  /-- Selected normal-positive functional/state representative. -/
  normalFunctional : Functional

  /-- The selected functional is normal-positive in the supplied standard form. -/
  normalFunctional_isNormalPositive :
    standardCone.isNormalPositive normalFunctional

  /-- Projective GW/count shadow. -/
  projectiveGW :
    GWProjectiveCountBridge G T Target Coeff

  /-- Reference/projective count profile for pairwise Weyl readouts. -/
  referenceCounts :
    CountProfile

  /-- Weyl gauge calibration for model states. -/
  weylGauge :
    ProjectiveWeylGaugeCalibration State

  /-- The state-space representative used by the projective-shadow bridge. -/
  state :
    State

  /-- Calibration: the bridge state is the Weyl state of the GW count pair. -/
  state_eq_weylState :
    state =
      weylGauge.stateOfProfiles
        projectiveGW.countState.counts
        referenceCounts
        projectiveGW.countState.support

  /-- Projective scaling action on model states. -/
  scaleState :
    ℝ → State → State

  /-- Weight `+2` GW/localization intensity readout. -/
  gwIntensity :
    State → ℝ

  /-- Weight `-2` inverse Weyl gauge readout. -/
  inverseWeylGauge :
    State → ℝ

  /-- Gauge-fixed physical volume/readout. -/
  physicalVolume :
    State → ℝ

  /-- GW intensity has projective weight `+2`. -/
  gwIntensity_weight_two :
    ∀ c : ℝ, ∀ s : State, c ≠ 0 →
      gwIntensity (scaleState c s) = c ^ 2 * gwIntensity s

  /-- The inverse Weyl gauge has projective weight `-2`. -/
  inverseWeylGauge_weight_minus_two :
    ∀ c : ℝ, ∀ s : State, c ≠ 0 →
      inverseWeylGauge (scaleState c s) = (c ^ 2)⁻¹ * inverseWeylGauge s

  /-- Physical volume is the product of intensity and inverse Weyl gauge. -/
  physicalVolume_True :
    ∀ s : State, physicalVolume s = gwIntensity s * inverseWeylGauge s

  /-- Optional backend certificate tying the standard-form sector to the state. -/
  standardForm_state_calibration : Prop

namespace StandardFormProjectiveGWBridge

variable (B : StandardFormProjectiveGWBridge (H := H) (Functional := Functional)
  (State := State) (G := G) (T := T) (Target := Target) (Coeff := Coeff))

/-- The selected normal functional has a standard-form natural-cone vector. -/
@[rep_depth projective]
theorem coneVector_mem_naturalCone :
    B.standardCone.coneVector B.normalFunctional ∈ B.standardCone.cone :=
  NaturalConeStandardFormInterface.coneVector_mem_of_normal
    B.standardCone B.normalFunctional B.normalFunctional_isNormalPositive

/-- The standard-form reflection fixes the selected cone vector. -/
@[rep_depth projective]
theorem J_fixes_coneVector :
    B.standardCone.J (B.standardCone.coneVector B.normalFunctional) =
      B.standardCone.coneVector B.normalFunctional :=
  NaturalConeStandardFormInterface.J_fixes_coneVector
    B.standardCone B.normalFunctional B.normalFunctional_isNormalPositive

/-- The projective count shape is invariant under nonzero rescaling. -/
@[rep_depth projective]
theorem normalizedShape_scale_counts
    (β c : ℝ) (hc : c ≠ 0) :
    finiteArithmeticNormalizedRay
        (fun n => c * B.projectiveGW.countState.counts n)
        B.projectiveGW.countState.support β =
      B.projectiveGW.countState.normalizedShape β :=
  B.projectiveGW.normalizedShape_scale_counts β c hc

/-- Weyl calibration readback: total equals scale times shape. -/
@[rep_depth projective]
theorem weyl_total_eq_scale_mul_shape
    (u : ℝ) :
    B.weylGauge.totalReadout B.state u =
      B.weylGauge.weylScaleReadout B.state u *
        B.weylGauge.shapeCoreReadout B.state u := by
  rw [B.state_eq_weylState]
  exact B.weylGauge.total_eq_scale_mul_shape
    B.projectiveGW.countState.counts
    B.referenceCounts
    B.projectiveGW.countState.support
    u

/--
Core projective-shadow cancellation:
weight `+2` GW intensity times weight `-2` inverse Weyl gauge is weight `0`.
-/
@[rep_depth projective]
theorem physicalVolume_scale_invariant
    (c : ℝ) (hc : c ≠ 0) (s : State) :
    B.physicalVolume (B.scaleState c s) = B.physicalVolume s := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  calc
    B.physicalVolume (B.scaleState c s)
        = B.gwIntensity (B.scaleState c s) *
            B.inverseWeylGauge (B.scaleState c s) := by
            rw [B.physicalVolume_True]
    _ = (c ^ 2 * B.gwIntensity s) * ((c ^ 2)⁻¹ * B.inverseWeylGauge s) := by
            rw [B.gwIntensity_weight_two c s hc,
              B.inverseWeylGauge_weight_minus_two c s hc]
    _ = B.gwIntensity s * B.inverseWeylGauge s := by
            field_simp [hc2]
    _ = B.physicalVolume s := by
            rw [B.physicalVolume_True]

end StandardFormProjectiveGWBridge

/-! ## Binary-word natural-cone face extension -/

@[rep_depth projective]
structure BinaryWordModularFaceBridge where
  naturalCone : Set (InfoGeometry.Krein.DoubledSpace H)
  localizationOp :
    TypeIIIModularCantorSystem.BinaryWord →
      InfoGeometry.Krein.DoubledSpace H →L[ℝ] InfoGeometry.Krein.DoubledSpace H
  cone_face_localization :
    ∀ (w : TypeIIIModularCantorSystem.BinaryWord)
      {ξ : InfoGeometry.Krein.DoubledSpace H},
      ξ ∈ naturalCone → localizationOp w ξ ∈ naturalCone

/-! ## Binary-word natural-cone face extension -/

/--
Projective-shadow bridge enriched with a theorem-safe binary-word natural-cone
face-localization socket.

This keeps the projective GW/Weyl cancellation layer separate from the
standard-form natural-cone face layer.  The face bridge is supplied as an
external witness; this file only transports its localization readback alongside
the projective volume cancellation theorem.
-/
@[rep_depth projective]
structure StandardFormProjectiveGWFaceBridge where
  /-- Existing standard-form projective GW/Weyl bridge. -/
  base :
    StandardFormProjectiveGWBridge (H := H) (Functional := Functional)
      (State := State) (G := G) (T := T) (Target := Target) (Coeff := Coeff)

  /-- Binary-word standard-form natural-cone face localization bridge. -/
  faceBridge :
    BinaryWordModularFaceBridge (H := H)

  /-- Optional certificate tying the projective state to the localized face data. -/
  face_state_calibration : Prop

namespace StandardFormProjectiveGWFaceBridge

variable (B : StandardFormProjectiveGWFaceBridge (H := H) (Functional := Functional)
  (State := State) (G := G) (T := T) (Target := Target) (Coeff := Coeff))

/-- Binary-word localization operator inherited from the standard-form face bridge. -/
@[rep_depth projective]
noncomputable def localizationOp
    (w : TypeIIIModularCantorSystem.BinaryWord) :
    InfoGeometry.Krein.DoubledSpace H →L[ℝ] InfoGeometry.Krein.DoubledSpace H :=
  BinaryWordModularFaceBridge.localizationOp B.faceBridge w

/--
Localized binary-word cone faces preserve the supplied natural cone.

This is a readback from `StandardFormNaturalConeBridge`, not a new analytic
Tomita--Takesaki theorem.
-/
@[rep_depth projective]
theorem cone_face_localization
    (w : TypeIIIModularCantorSystem.BinaryWord)
    {ξ : InfoGeometry.Krein.DoubledSpace H}
    (hξ : ξ ∈ B.faceBridge.naturalCone) :
    StandardFormProjectiveGWFaceBridge.localizationOp B w ξ ∈
      B.faceBridge.naturalCone :=
  BinaryWordModularFaceBridge.cone_face_localization B.faceBridge w hξ

/-- The base projective GW/Weyl volume readout remains scale invariant. -/
@[rep_depth projective]
theorem physicalVolume_scale_invariant
    (c : ℝ) (hc : c ≠ 0) (s : State) :
    B.base.physicalVolume (B.base.scaleState c s) = B.base.physicalVolume s :=
  StandardFormProjectiveGWBridge.physicalVolume_scale_invariant B.base c hc s

end StandardFormProjectiveGWFaceBridge

end Core

end InfoGeometry.Canonical.StandardFormProjectiveGWBridge
