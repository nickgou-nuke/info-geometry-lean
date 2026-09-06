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
import InfoGeometry.Optics.JonesCalibration
import InfoGeometry.OperatorAlgebra.StinespringDilation
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SusceptibilityHessian

open InfoGeometry.Optics.JonesCalibration
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

/--
The Hessian degeneracy boundary.

This is the optical/material response boundary used by snap and singular
response modules.  It is just the named singular locus of the Hessian datum.
-/
def IsHessianDegenerate
    {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]
    (H : HessianResponseDatum State)
    (U : State) : Prop :=
  H.singularAt U

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

  material_law_holds :
    material_law

namespace MaterialResponseModel

variable {State : Type*}
variable (M : MaterialResponseModel State)

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

  hessian_controls_susceptibility_holds :
    hessian_controls_susceptibility

  /-- Regular states have a valid material response in the chosen model. -/
  regular_response_law :
    ∀ U : State, H.regularAt U → Prop

  regular_response_holds :
    ∀ U : State, ∀ hU : H.regularAt U, regular_response_law U hU

namespace HessianSusceptibilityCalibration

variable {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]
variable {H : HessianResponseDatum State}
variable {M : MaterialResponseModel State}
variable (C : HessianSusceptibilityCalibration State H M)

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

  fresnel_law_holds :
    fresnel_law

namespace FresnelCoefficientReadout

variable {State : Type*}
variable (F : FresnelCoefficientReadout State)

end FresnelCoefficientReadout

/-! ## 3a. State-level polarization eigen-response -/

/--
Eigen-response of the susceptibility/Hessian in the `s/p` polarization basis.

This is a state-indexed calibration socket: a concrete material/interface
model supplies the laws saying these are the local eigenchannel readouts.
-/
structure StatePolarizationEigenResponse
    (State : Type*) where
  /-- Geometric/material response in the `s` channel. -/
  responseS : State → ℂ

  /-- Geometric/material response in the `p` channel. -/
  responseP : State → ℂ

  /-- Certificate that `responseS` is the calibrated `s` eigen-response. -/
  s_eigen_law : Prop

  s_eigen_law_holds :
    s_eigen_law

  /-- Certificate that `responseP` is the calibrated `p` eigen-response. -/
  p_eigen_law : Prop

  p_eigen_law_holds :
    p_eigen_law

namespace StatePolarizationEigenResponse

variable {State : Type*}
variable (E : StatePolarizationEigenResponse State)

end StatePolarizationEigenResponse

/--
Calibration saying Fresnel coefficients are obtained from the calibrated
state-level polarization eigen-responses.
-/
structure FresnelFromStateEigenResponse
    (State : Type*)
    (E : StatePolarizationEigenResponse State)
    (F : FresnelCoefficientReadout State) where
  /-- The `s` Fresnel coefficient is the `s` eigen-response. -/
  rs_eq_responseS :
    ∀ U : State, F.rs U = E.responseS U

  /-- The `p` Fresnel coefficient is the `p` eigen-response. -/
  rp_eq_responseP :
    ∀ U : State, F.rp U = E.responseP U

namespace FresnelFromStateEigenResponse

variable {State : Type*}
variable {E : StatePolarizationEigenResponse State}
variable {F : FresnelCoefficientReadout State}

/-- The `s` response readout is the Fresnel `r_s`. -/
theorem responseS_eq_rs
    (C : FresnelFromStateEigenResponse State E F)
    (U : State) :
    E.responseS U = F.rs U :=
  (FresnelFromStateEigenResponse.rs_eq_responseS C U).symm

/-- The `p` response readout is the Fresnel `r_p`. -/
theorem responseP_eq_rp
    (C : FresnelFromStateEigenResponse State E F)
    (U : State) :
    E.responseP U = F.rp U :=
  (FresnelFromStateEigenResponse.rp_eq_responseP C U).symm

end FresnelFromStateEigenResponse

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
  coherence := F.fresnel_law

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

/--
The calibrated Jones matrix is diagonal in the local `s/p` eigenbasis.
-/
theorem jones_offdiag_01_zero
    (U : State) :
    (C.eventOf U).jones 0 1 = 0 :=
  JonesOpticalEvent.jones_apply_offdiag_zero_one (C.eventOf U)

/--
The calibrated Jones matrix is diagonal in the local `s/p` eigenbasis.
-/
theorem jones_offdiag_10_zero
    (U : State) :
    (C.eventOf U).jones 1 0 = 0 :=
  JonesOpticalEvent.jones_apply_offdiag_one_zero (C.eventOf U)

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

  retardance_law_holds :
    retardance_law

  /-- Ellipticity law, separated for modules that only need amplitude/shape data. -/
  ellipticity_law : Prop

  ellipticity_law_holds :
    ellipticity_law

namespace RetardanceReadout

variable {State : Type*}
variable (R : RetardanceReadout State)

end RetardanceReadout

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

  hessian_controls_optical_response_holds :
    hessian_controls_optical_response

  /-- Absorption readout is calibrated to Bregman heat. -/
  absorption_matches_bregman_heat : Prop

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

/-- The calibrated Jones matrix is diagonal in the local `s/p` eigenbasis. -/
theorem jones_offdiag_01_zero
    (U : State) :
    (C.eventOf U).jones 0 1 = 0 :=
  C.jonesCalibration.jones_offdiag_01_zero U

/-- The calibrated Jones matrix is diagonal in the local `s/p` eigenbasis. -/
theorem jones_offdiag_10_zero
    (U : State) :
    (C.eventOf U).jones 1 0 = 0 :=
  C.jonesCalibration.jones_offdiag_10_zero U

end OpticalResponseCalibration

/--
Full state-level optical response calibration with explicit polarization
eigen-response.

This extends the compatibility surface without replacing the older
`OpticalResponseCalibration` API.  The Fresnel data are still witness-gated by
the supplied material and boundary calibration.
-/
structure OpticalResponseEigenCalibration
    (State : Type*) [NormedAddCommGroup State] [NormedSpace ℝ State]
    (H : HessianResponseDatum State)
    (M : MaterialResponseModel State)
    (E : StatePolarizationEigenResponse State)
    (F : FresnelCoefficientReadout State) where
  /-- Hessian-to-susceptibility calibration. -/
  hessianSusceptibility :
    HessianSusceptibilityCalibration State H M

  /-- Fresnel coefficients as calibrated eigen-response readouts. -/
  fresnelFromEigen :
    FresnelFromStateEigenResponse State E F

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

  hessian_controls_optical_response_holds :
    hessian_controls_optical_response

  /-- Absorption readout is calibrated to Bregman heat. -/
  absorption_matches_bregman_heat : Prop

  absorption_matches_bregman_heat_holds :
    absorption_matches_bregman_heat

  /-- Retardance/ellipticity is calibrated by the Hessian eigen-response. -/
  hessian_controls_retardance : Prop

  hessian_controls_retardance_holds :
    hessian_controls_retardance

namespace OpticalResponseEigenCalibration

variable {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]
variable {H : HessianResponseDatum State}
variable {M : MaterialResponseModel State}
variable {E : StatePolarizationEigenResponse State}
variable {F : FresnelCoefficientReadout State}

/-- The `s` eigen-response readout is the Fresnel `r_s`. -/
theorem responseS_eq_rs
    (C : OpticalResponseEigenCalibration State H M E F)
    (U : State) :
    E.responseS U = F.rs U :=
  FresnelFromStateEigenResponse.responseS_eq_rs C.fresnelFromEigen U

/-- The `p` eigen-response readout is the Fresnel `r_p`. -/
theorem responseP_eq_rp
    (C : OpticalResponseEigenCalibration State H M E F)
    (U : State) :
    E.responseP U = F.rp U :=
  FresnelFromStateEigenResponse.responseP_eq_rp C.fresnelFromEigen U

/-- The calibrated Jones matrix has `r_s` in the first diagonal channel. -/
theorem jones_00_eq_rs
    (C : OpticalResponseEigenCalibration State H M E F)
    (U : State) :
    (C.jonesCalibration.eventOf U).jones 0 0 = F.rs U :=
  C.jonesCalibration.jones_00_eq_rs U

/-- The calibrated Jones matrix has `r_p` in the second diagonal channel. -/
theorem jones_11_eq_rp
    (C : OpticalResponseEigenCalibration State H M E F)
    (U : State) :
    (C.jonesCalibration.eventOf U).jones 1 1 = F.rp U :=
  C.jonesCalibration.jones_11_eq_rp U

end OpticalResponseEigenCalibration

/-! ## 5. Material-response bridge with Fresnel eigenvalues -/

/--
Information potential with a Hessian-style response pairing.

Complex optical coefficients are readouts of calibrated material/operator
response, not consequences of bare algebra alone.
-/
structure InformationPotentialDatum
    (State Tangent : Type*) where
  /-- Information potential. -/
  potential : State → ℝ

  /-- Hessian response pairing. -/
  hessian : State → Tangent → Tangent → ℝ

  /-- Symmetry of the Hessian. -/
  symmetric :
    ∀ X xi eta, hessian X xi eta = hessian X eta xi

  /-- Positive-semidefinite response. -/
  positive_semidefinite :
    ∀ X xi, 0 ≤ hessian X xi xi

namespace InformationPotentialDatum

variable {State Tangent : Type*}
variable (Phi : InformationPotentialDatum State Tangent)

/-- Re-export Hessian symmetry. -/
theorem hessian_symmetric
    (X : State)
    (xi eta : Tangent) :
    Phi.hessian X xi eta = Phi.hessian X eta xi :=
  Phi.symmetric X xi eta

/-- Re-export positive semidefiniteness. -/
theorem hessian_nonneg
    (X : State)
    (xi : Tangent) :
    0 ≤ Phi.hessian X xi xi :=
  Phi.positive_semidefinite X xi

end InformationPotentialDatum

/--
Bregman-style heat/readout datum.

Concrete modules can instantiate this with an explicit Bregman divergence,
such as the finite Jones quadratic potential.
-/
structure BregmanHeatDatum
    (State : Type*) where
  /-- Heat/divergence readout. -/
  heat : State → State → ℝ

  /-- Nonnegativity of the heat readout. -/
  nonnegative :
    ∀ X Y, 0 ≤ heat X Y

  /-- Vanishing on the diagonal. -/
  zero_on_diagonal :
    ∀ X, heat X X = 0

namespace BregmanHeatDatum

variable {State : Type*}
variable (B : BregmanHeatDatum State)

/-- Re-export heat nonnegativity. -/
theorem heat_nonnegative
    (X Y : State) :
    0 ≤ B.heat X Y :=
  B.nonnegative X Y

/-- Re-export diagonal vanishing. -/
theorem heat_self
    (X : State) :
    B.heat X X = 0 :=
  B.zero_on_diagonal X

end BregmanHeatDatum

/--
Abstract linear susceptibility datum.

`Op` is the material/operator response algebra.  `Freq` and `WaveVector`
parametrize the frequency and momentum/wave-vector channels.
-/
structure LinearSusceptibilityDatum
    (Op Freq WaveVector : Type*) where
  /-- Frequency/wave-vector dependent susceptibility. -/
  susceptibility : Freq → WaveVector → Op → Op

  /-- Causality/retarded-response certificate. -/
  causal : Prop

  /-- Kubo or linear-response origin certificate. -/
  linearResponseOrigin : Prop

  /-- Compatibility with a Hessian information response. -/
  hessianCompatibility : Prop

/--
Hessian-to-susceptibility bridge for a concrete material model.

This is where a concrete material proves that its response is induced by the
Hessian of the chosen information potential.
-/
structure HessianSusceptibilityBridge
    (State Tangent Op Freq WaveVector : Type*) where
  /-- Information potential and Hessian response. -/
  potential :
    InformationPotentialDatum State Tangent

  /-- Linear susceptibility datum. -/
  susceptibility :
    LinearSusceptibilityDatum Op Freq WaveVector

  /-- Material state at which response is linearized. -/
  baseState : State

  /-- Map from operator perturbations to Hessian tangent directions. -/
  tangentOfPerturbation : Op → Tangent

  /-- Certificate that susceptibility is induced by the Hessian response. -/
  susceptibility_eq_hessian_response : Prop

/--
Dielectric/impedance response extracted from susceptibility.

This material socket is needed before Fresnel coefficients can be computed.
-/
structure DielectricResponseDatum
    (Freq WaveVector : Type*) where
  /-- Complex dielectric response. -/
  epsilon : Freq → WaveVector → ℂ

  /-- Complex permeability response. -/
  mu : Freq → WaveVector → ℂ

  /-- Complex refractive index. -/
  refractiveIndex : Freq → WaveVector → ℂ

  /-- Complex impedance. -/
  impedance : Freq → WaveVector → ℂ

  /-- Optical backend validity certificate. -/
  opticalBackendValid : Prop

  /-- Compatibility with a susceptibility datum. -/
  fromSusceptibility : Prop

/-- Polarization mode at a planar interface. -/
inductive PolarizationMode where
  | s
  | p
deriving DecidableEq, Repr

/--
Interface response data sufficient for Fresnel formulas.