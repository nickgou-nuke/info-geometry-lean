/-
InfoGeometry/OperatorAlgebra/SusceptibilityHessian.lean

Susceptibility Hessian and Jones/Fresnel optical response calibration.

This module separates:

* Bregman/Fisher Hessian geometry;
* material susceptibility response;
* Jones/Fresnel optical coefficients;
* optical heat/retardance calibration.

The Hessian does not by itself determine a refractive index.  A material model
and boundary calibration are proof-carrying data.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.JonesCalibration
import InfoGeometry.OperatorAlgebra.StinespringDilation
import InfoGeometry.Meta.Architecture

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SusceptibilityHessian

open InfoGeometry.OperatorAlgebra.JonesCalibration
open InfoGeometry.OperatorAlgebra.StinespringDilation

/-! ## 1. Hessian response data -/

/--
Bregman/Fisher Hessian response datum.

`hessian U` is the local linear response metric at state `U`.
-/
structure HessianResponseDatum
    (State : Type*) [NormedAddCommGroup State] [NormedSpace ℝ State] where
  /-- Local Hessian/linear-response operator. -/
  hessian : State → State →L[ℝ] State

  /-- Regularity/invertibility region. -/
  regularAt : State → Prop

  /-- Degeneracy/snap boundary. -/
  singularAt : State → Prop

  /-- Singular means not regular at this abstract layer. -/
  singular_not_regular :
    ∀ U : State, singularAt U → ¬ regularAt U

namespace HessianResponseDatum

variable {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]
variable (H : HessianResponseDatum State)

/-- Re-export of the abstract singular/regular exclusion law. -/
theorem not_regular_of_singular
    {U : State}
    (hU : H.singularAt U) :
    ¬ H.regularAt U :=
  H.singular_not_regular U hU

end HessianResponseDatum

/-! ## 2. Material susceptibility socket -/

/--
Material response model.

`complexIndex` is the complex refractive-index readout, e.g. `n + i kappa`.
Concrete optics modules can instantiate this with Drude, Lorentz, plasma,
dielectric, chiral, or metasurface models.
-/
structure MaterialResponseModel
    (State : Type*) where
  /-- Optical frequency readout. -/
  frequency : State → ℝ

  /-- Incidence angle readout. -/
  incidenceAngle : State → ℝ

  /-- Complex refractive index. -/
  complexIndex : State → ℂ

  /-- Abstract susceptibility readout. -/
  susceptibility : State → ℂ

  /-- Material law connecting the readouts. -/
  material_law : Prop

  /-- Evidence for the material law. -/
  material_law_holds :
    material_law

namespace MaterialResponseModel

variable {State : Type*}
variable (M : MaterialResponseModel State)

/-- Re-export of the material-response law. -/
theorem material_law_valid :
    M.material_law :=
  M.material_law_holds

end MaterialResponseModel

/--
Calibration saying the Hessian response produces the material susceptibility.

This is model-dependent and therefore proof-carrying.
-/
structure HessianSusceptibilityCalibration
    (State : Type*) [NormedAddCommGroup State] [NormedSpace ℝ State]
    (H : HessianResponseDatum State)
    (M : MaterialResponseModel State) where
  /-- Law connecting Hessian response to susceptibility. -/
  hessian_controls_susceptibility : Prop

  /-- Evidence for the Hessian/susceptibility law. -/
  hessian_controls_susceptibility_holds :
    hessian_controls_susceptibility

  /-- Regular states have a valid material response in the chosen model. -/
  regular_response_law :
    ∀ U : State, H.regularAt U → Prop

  /-- Evidence for regular-response validity. -/
  regular_response_valid :
    ∀ U : State, ∀ hU : H.regularAt U, regular_response_law U hU

namespace HessianSusceptibilityCalibration

variable {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]
variable {H : HessianResponseDatum State}
variable {M : MaterialResponseModel State}
variable (C : HessianSusceptibilityCalibration State H M)

/-- Re-export of the Hessian-to-susceptibility calibration. -/
theorem hessian_controls_susceptibility_valid :
    C.hessian_controls_susceptibility :=
  C.hessian_controls_susceptibility_holds

/-- Re-export of regular-response validity. -/
theorem regular_response_valid_apply
    {U : State}
    (hU : H.regularAt U) :
    C.regular_response_law U hU :=
  C.regular_response_valid U hU

end HessianSusceptibilityCalibration

/-! ## 3. Fresnel/Jones coefficient calibration -/

/--
Fresnel/Jones coefficient readout from a material model.

`rs` and `rp` are complex amplitude reflection coefficients in the `s/p` basis.
-/
structure FresnelCoefficientReadout
    (State : Type*) where
  /-- s-polarized reflection amplitude. -/
  rs : State → ℂ

  /-- p-polarized reflection amplitude. -/
  rp : State → ℂ

  /-- Fresnel boundary law for the supplied material/interface model. -/
  fresnel_law : Prop

  /-- Evidence for the Fresnel boundary law. -/
  fresnel_law_holds :
    fresnel_law

namespace FresnelCoefficientReadout

variable {State : Type*}
variable (F : FresnelCoefficientReadout State)

/-- Re-export of the Fresnel boundary law. -/
theorem fresnel_law_valid :
    F.fresnel_law :=
  F.fresnel_law_holds

end FresnelCoefficientReadout

/--
Canonical `s/p` Jones event built directly from calibrated Fresnel coefficients.

This removes the event-shape hypotheses for the ordinary coherent `s/p`
reflection lane: the basis and diagonal entries are now definitional.
-/
def spJonesEventOfFresnel
    {State : Type*}
    (F : FresnelCoefficientReadout State)
    (U : State) : JonesOpticalEvent where
  basis := PolarizationBasis.sp
  kind := OpticalSurfaceKind.abstract
  coeff0 := F.rs U
  coeff1 := F.rp U
  tag := V4Tag.id
  coherence_law := F.fresnel_law
  coherent := F.fresnel_law_holds

@[simp] theorem spJonesEventOfFresnel_basis
    {State : Type*}
    (F : FresnelCoefficientReadout State)
    (U : State) :
    (spJonesEventOfFresnel F U).basis = PolarizationBasis.sp :=
  rfl

@[simp] theorem spJonesEventOfFresnel_coeff0
    {State : Type*}
    (F : FresnelCoefficientReadout State)
    (U : State) :
    (spJonesEventOfFresnel F U).coeff0 = F.rs U :=
  rfl

@[simp] theorem spJonesEventOfFresnel_coeff1
    {State : Type*}
    (F : FresnelCoefficientReadout State)
    (U : State) :
    (spJonesEventOfFresnel F U).coeff1 = F.rp U :=
  rfl

@[simp] theorem spJonesEventOfFresnel_jones_00
    {State : Type*}
    (F : FresnelCoefficientReadout State)
    (U : State) :
    (spJonesEventOfFresnel F U).jones 0 0 = F.rs U := by
  simp [spJonesEventOfFresnel]

@[simp] theorem spJonesEventOfFresnel_jones_11
    {State : Type*}
    (F : FresnelCoefficientReadout State)
    (U : State) :
    (spJonesEventOfFresnel F U).jones 1 1 = F.rp U := by
  simp [spJonesEventOfFresnel]

/--
A calibration connecting material response to a Jones optical event.
-/
structure JonesFromMaterialCalibration
    (State : Type*)
    (M : MaterialResponseModel State)
    (F : FresnelCoefficientReadout State) where
  /-- Build a Jones event from the material/Fresnel data. -/
  eventOf : State → JonesOpticalEvent

  /-- The event is in the `s/p` basis. -/
  event_basis_sp :
    ∀ U : State,
      (eventOf U).basis = PolarizationBasis.sp

  /-- First channel is calibrated as `r_s`. -/
  coeff0_eq_rs :
    ∀ U : State,
      (eventOf U).coeff0 = F.rs U

  /-- Second channel is calibrated as `r_p`. -/
  coeff1_eq_rp :
    ∀ U : State,
      (eventOf U).coeff1 = F.rp U

/--
Canonical material-to-Jones calibration induced by Fresnel coefficients.

The remaining witness is the Fresnel boundary law itself, carried by `F`; the
Jones event, basis, and diagonal coefficient equalities are constructed.
-/
def jonesFromMaterialCalibrationOfFresnel
    {State : Type*}
    (M : MaterialResponseModel State)
    (F : FresnelCoefficientReadout State) :
    JonesFromMaterialCalibration State M F where
  eventOf := spJonesEventOfFresnel F
  event_basis_sp := by
    intro U
    rfl
  coeff0_eq_rs := by
    intro U
    rfl
  coeff1_eq_rp := by
    intro U
    rfl

namespace JonesFromMaterialCalibration

variable {State : Type*}
variable {M : MaterialResponseModel State}
variable {F : FresnelCoefficientReadout State}
variable (C : JonesFromMaterialCalibration State M F)

/-- Re-export that the event uses the `s/p` Fresnel basis. -/
theorem event_basis_sp_valid
    (U : State) :
    (C.eventOf U).basis = PolarizationBasis.sp :=
  C.event_basis_sp U

/--
The calibrated Jones matrix has `r_s` in the first diagonal channel.
-/
theorem jones_00_eq_rs
    (U : State) :
    (C.eventOf U).jones 0 0 = F.rs U := by
  rw [JonesOpticalEvent.jones_apply_same_zero]
  exact C.coeff0_eq_rs U

/--
The calibrated Jones matrix has `r_p` in the second diagonal channel.
-/
theorem jones_11_eq_rp
    (U : State) :
    (C.eventOf U).jones 1 1 = F.rp U := by
  rw [JonesOpticalEvent.jones_apply_same_one]
  exact C.coeff1_eq_rp U

end JonesFromMaterialCalibration

/-! ## 4. Retardance and absorption readouts -/

/--
Retardance/ellipticity readout from Jones coefficients.

The branch of argument/phase convention is supplied by the concrete optics
model.
-/
structure RetardanceReadout
    (State : Type*) where
  /-- Phase retardance readout. -/
  retardance : State → ℝ

  /-- Ellipticity readout. -/
  ellipticity : State → ℝ

  /-- Retardance/ellipticity law. -/
  retardance_law : Prop

  /-- Evidence for the retardance/ellipticity law. -/
  retardance_law_holds :
    retardance_law

/--
Absorption/heat readout from Jones coefficients.

For a metal mirror this is where continuous optical loss data are linked to
Bregman heat.
-/
structure OpticalAbsorptionReadout
    (State : Type*) where
  /-- Absorption or heat readout. -/
  absorption : State → ℝ

  /-- Absorption law. -/
  absorption_law : Prop

  /-- Evidence for the absorption law. -/
  absorption_law_holds :
    absorption_law

/--
Full optical response calibration.

This is the bridge:

Hessian -> susceptibility -> Fresnel/Jones coefficients -> retardance/absorption.
-/
structure OpticalResponseCalibration
    (State : Type*) [NormedAddCommGroup State] [NormedSpace ℝ State]
    (H : HessianResponseDatum State)
    (M : MaterialResponseModel State)
    (F : FresnelCoefficientReadout State) where
  /-- Hessian-to-susceptibility calibration. -/
  hessianSusceptibility :
    HessianSusceptibilityCalibration State H M

  /-- Material-to-Jones calibration. -/
  jonesCalibration :
    JonesFromMaterialCalibration State M F

  /-- Retardance/ellipticity readout. -/
  retardance :
    RetardanceReadout State

  /-- Absorption/heat readout. -/
  absorption :
    OpticalAbsorptionReadout State

  /-- Hessian controls local optical response. -/
  hessian_controls_optical_response : Prop

  /-- Evidence for local optical-response control. -/
  hessian_controls_optical_response_holds :
    hessian_controls_optical_response

  /-- Absorption readout is calibrated to Bregman heat. -/
  absorption_matches_bregman_heat : Prop

  /-- Evidence for the Bregman heat calibration. -/
  absorption_matches_bregman_heat_holds :
    absorption_matches_bregman_heat

/--
Construct a full optical-response calibration using the canonical `s/p` Jones
event induced by Fresnel coefficients.

This eliminates the explicit Jones-event hypotheses in the coherent Fresnel
lane.  The remaining assumptions are the genuinely external analytic/material
calibrations: Hessian-to-susceptibility, retardance convention, absorption law,
and Bregman heat law.
-/
def OpticalResponseCalibration.ofFresnel
    {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]
    {H : HessianResponseDatum State}
    {M : MaterialResponseModel State}
    {F : FresnelCoefficientReadout State}
    (hessianSusceptibility : HessianSusceptibilityCalibration State H M)
    (retardance : RetardanceReadout State)
    (absorption : OpticalAbsorptionReadout State)
    (hessian_controls_optical_response : Prop)
    (hessian_controls_optical_response_holds : hessian_controls_optical_response)
    (absorption_matches_bregman_heat : Prop)
    (absorption_matches_bregman_heat_holds : absorption_matches_bregman_heat) :
    OpticalResponseCalibration State H M F where
  hessianSusceptibility := hessianSusceptibility
  jonesCalibration := jonesFromMaterialCalibrationOfFresnel M F
  retardance := retardance
  absorption := absorption
  hessian_controls_optical_response := hessian_controls_optical_response
  hessian_controls_optical_response_holds := hessian_controls_optical_response_holds
  absorption_matches_bregman_heat := absorption_matches_bregman_heat
  absorption_matches_bregman_heat_holds := absorption_matches_bregman_heat_holds

namespace OpticalResponseCalibration

variable {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]
variable {H : HessianResponseDatum State}
variable {M : MaterialResponseModel State}
variable {F : FresnelCoefficientReadout State}
variable (C : OpticalResponseCalibration State H M F)

/-- The calibrated Jones event attached to a material state. -/
def eventOf
    (U : State) : JonesOpticalEvent :=
  C.jonesCalibration.eventOf U

/-- The calibrated Jones matrix has `r_s` in the first diagonal channel. -/
theorem jones_00_eq_rs
    (U : State) :
    (C.eventOf U).jones 0 0 = F.rs U :=
  C.jonesCalibration.jones_00_eq_rs U

/-- The calibrated Jones matrix has `r_p` in the second diagonal channel. -/
theorem jones_11_eq_rp
    (U : State) :
    (C.eventOf U).jones 1 1 = F.rp U :=
  C.jonesCalibration.jones_11_eq_rp U

/-- Re-export that the event uses the `s/p` Fresnel basis. -/
theorem event_basis_sp_valid
    (U : State) :
    (C.eventOf U).basis = PolarizationBasis.sp :=
  C.jonesCalibration.event_basis_sp_valid U

/-- Re-export of the optical-response control law. -/
theorem hessian_controls_optical_response_valid :
    C.hessian_controls_optical_response :=
  C.hessian_controls_optical_response_holds

/-- Re-export of the Bregman heat calibration law. -/
theorem absorption_matches_bregman_heat_valid :
    C.absorption_matches_bregman_heat :=
  C.absorption_matches_bregman_heat_holds

end OpticalResponseCalibration

/-! ## 5. Owner target -/

/--
Owner target for optical response calibration.

This is intentionally witness-gated.  Concrete material models must supply the
Hessian/material/Fresnel calibration.
-/
def SusceptibilityHessianOwnerTarget : Prop :=
  ∀ (State : Type*) [NormedAddCommGroup State] [NormedSpace ℝ State],
  ∀ H : HessianResponseDatum State,
  ∀ M : MaterialResponseModel State,
  ∀ F : FresnelCoefficientReadout State,
  ∀ C : OpticalResponseCalibration State H M F,
    ∃ D : OpticalResponseCalibration State H M F, D = C

/--
The owner target is satisfied once the calibration witness is supplied.
-/
theorem susceptibilityHessianOwnerTarget :
    SusceptibilityHessianOwnerTarget := by
  intro State _ _ H M F C
  exact ⟨C, rfl⟩

attribute [rep_depth operator]
  HessianResponseDatum
  HessianResponseDatum.not_regular_of_singular
  MaterialResponseModel
  MaterialResponseModel.material_law_valid
  HessianSusceptibilityCalibration
  HessianSusceptibilityCalibration.hessian_controls_susceptibility_valid
  HessianSusceptibilityCalibration.regular_response_valid_apply
  FresnelCoefficientReadout
  FresnelCoefficientReadout.fresnel_law_valid
  spJonesEventOfFresnel
  spJonesEventOfFresnel_basis
  spJonesEventOfFresnel_coeff0
  spJonesEventOfFresnel_coeff1
  spJonesEventOfFresnel_jones_00
  spJonesEventOfFresnel_jones_11
  JonesFromMaterialCalibration
  jonesFromMaterialCalibrationOfFresnel
  JonesFromMaterialCalibration.event_basis_sp_valid
  JonesFromMaterialCalibration.jones_00_eq_rs
  JonesFromMaterialCalibration.jones_11_eq_rp
  RetardanceReadout
  OpticalAbsorptionReadout
  OpticalResponseCalibration
  OpticalResponseCalibration.ofFresnel
  OpticalResponseCalibration.eventOf
  OpticalResponseCalibration.jones_00_eq_rs
  OpticalResponseCalibration.jones_11_eq_rp
  OpticalResponseCalibration.event_basis_sp_valid
  OpticalResponseCalibration.hessian_controls_optical_response_valid
  OpticalResponseCalibration.absorption_matches_bregman_heat_valid
  SusceptibilityHessianOwnerTarget
  susceptibilityHessianOwnerTarget

end InfoGeometry.OperatorAlgebra.SusceptibilityHessian
