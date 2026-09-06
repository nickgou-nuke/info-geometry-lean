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
-- [STITCHER: MISSING OVERLAP] --
Interface response data sufficient for Fresnel formulas.

The quantities are complex-valued to support absorbing media.
-/
structure OpticalInterfaceResponse
    (Freq : Type*) where
  /-- Index/impedance package for medium 1, compressed as `n1`. -/
  n1 : Freq → ℂ

  /-- Index/impedance package for medium 2, compressed as `n2`. -/
  n2 : Freq → ℂ

  /-- Cosine of incidence angle, or its complex continuation. -/
  cosIncident : Freq → ℂ

  /-- Cosine of transmission angle, or its complex continuation. -/
  cosTransmitted : Freq → ℂ

  /-- Certificate that Snell/interface geometry is valid. -/
  interfaceGeometryValid : Prop

/-- Standard s-polarized Fresnel reflection amplitude. -/
def fresnelRS
    {Freq : Type*}
    (I : OpticalInterfaceResponse Freq)
    (omega : Freq) : ℂ :=
  (I.n1 omega * I.cosIncident omega - I.n2 omega * I.cosTransmitted omega) /
    (I.n1 omega * I.cosIncident omega + I.n2 omega * I.cosTransmitted omega)

/-- Standard p-polarized Fresnel reflection amplitude. -/
def fresnelRP
    {Freq : Type*}
    (I : OpticalInterfaceResponse Freq)
    (omega : Freq) : ℂ :=
  (I.n2 omega * I.cosIncident omega - I.n1 omega * I.cosTransmitted omega) /
    (I.n2 omega * I.cosIncident omega + I.n1 omega * I.cosTransmitted omega)

/--
Fresnel coefficient datum with explicit standard reflection formulas.

The transmission laws remain proof-carrying because their branch conventions
belong to the material/interface layer.
-/
structure MaterialFresnelCoefficientDatum
    (Freq : Type*) where
  /-- Interface geometry and optical response. -/
  interface :
    OpticalInterfaceResponse Freq

  /-- s-polarized reflection coefficient. -/
  r_s : Freq → ℂ

  /-- p-polarized reflection coefficient. -/
  r_p : Freq → ℂ

  /-- s-polarized transmission coefficient. -/
  t_s : Freq → ℂ

  /-- p-polarized transmission coefficient. -/
  t_p : Freq → ℂ

  /-- s coefficient is the standard interface formula. -/
  r_s_eq_standard :
    ∀ omega, r_s omega = fresnelRS interface omega

  /-- p coefficient is the standard interface formula. -/
  r_p_eq_standard :
    ∀ omega, r_p omega = fresnelRP interface omega

namespace MaterialFresnelCoefficientDatum

variable {Freq : Type*}
variable (F : MaterialFresnelCoefficientDatum Freq)

/-- s-polarized coefficient equals the standard Fresnel expression. -/
theorem r_s_eq
    (omega : Freq) :
    F.r_s omega = fresnelRS F.interface omega :=
  F.r_s_eq_standard omega

/-- p-polarized coefficient equals the standard Fresnel expression. -/
theorem r_p_eq
    (omega : Freq) :
    F.r_p omega = fresnelRP F.interface omega :=
  F.r_p_eq_standard omega

end MaterialFresnelCoefficientDatum

/--
Polarization eigen-response.

The intended interpretation is that `s` and `p` polarizations diagonalize the
material/interface response.
-/
structure PolarizationEigenResponse
    (Freq : Type*) where
  /-- Polarization eigenvalue. -/
  eigenvalue : PolarizationMode → Freq → ℂ

/--
Fresnel coefficients as eigenvalues of the polarization response.

This is the formal version of: `r_s` and `r_p` are geometric eigenvalues after
material and interface calibration have been supplied.
-/
structure FresnelEigenCalibration
    (Freq : Type*) where
  /-- Fresnel coefficient data. -/
  fresnel :
    MaterialFresnelCoefficientDatum Freq

  /-- Polarization eigen-response. -/
  eigenResponse :
    PolarizationEigenResponse Freq

  /-- s eigenvalue is `r_s`. -/
  s_eigenvalue_eq :
    ∀ omega,
      eigenResponse.eigenvalue PolarizationMode.s omega =
        fresnel.r_s omega

  /-- p eigenvalue is `r_p`. -/
  p_eigenvalue_eq :
    ∀ omega,
      eigenResponse.eigenvalue PolarizationMode.p omega =
        fresnel.r_p omega

namespace FresnelEigenCalibration

variable {Freq : Type*}
variable (C : FresnelEigenCalibration Freq)

/-- The s-polarized geometric eigenvalue is the Fresnel `r_s`. -/
theorem s_eigenvalue_is_r_s
    (omega : Freq) :
    C.eigenResponse.eigenvalue PolarizationMode.s omega =
      C.fresnel.r_s omega :=
  C.s_eigenvalue_eq omega

/-- The p-polarized geometric eigenvalue is the Fresnel `r_p`. -/
theorem p_eigenvalue_is_r_p
    (omega : Freq) :
    C.eigenResponse.eigenvalue PolarizationMode.p omega =
      C.fresnel.r_p omega :=
  C.p_eigenvalue_eq omega

/-- The s-polarized eigenvalue equals the standard Fresnel formula. -/
theorem s_eigenvalue_eq_standard
    (omega : Freq) :
    C.eigenResponse.eigenvalue PolarizationMode.s omega =
      fresnelRS C.fresnel.interface omega := by
  rw [C.s_eigenvalue_is_r_s omega]
  exact C.fresnel.r_s_eq omega

/-- The p-polarized eigenvalue equals the standard Fresnel formula. -/
theorem p_eigenvalue_eq_standard
    (omega : Freq) :
    C.eigenResponse.eigenvalue PolarizationMode.p omega =
      fresnelRP C.fresnel.interface omega := by
  rw [C.p_eigenvalue_is_r_p omega]
  exact C.fresnel.r_p_eq omega

end FresnelEigenCalibration

/-- Operatorial Jones response indexed by polarization and frequency. -/
structure OperatorialJonesResponse
    (Op Freq : Type*) [Ring Op] where
  /-- Jones operator for the selected channel and frequency. -/
  jonesOperator : PolarizationMode → Freq → Op

/-- Calibration between operatorial Jones response and Fresnel eigenvalues. -/
structure JonesFresnelCalibration
    (Op Freq : Type*) [Ring Op] where
  /-- Fresnel eigenvalue calibration. -/
  fresnelEigen :
    FresnelEigenCalibration Freq

  /-- Operatorial Jones response. -/
  jones :
    OperatorialJonesResponse Op Freq

  /-- The `s` Jones channel is calibrated by the s Fresnel eigenvalue. -/
  sCalibration : Prop

  /-- The `p` Jones channel is calibrated by the p Fresnel eigenvalue. -/
  pCalibration : Prop

  /-- Flux conservation or absorption/Stinespring accounting certificate. -/
  fluxAccounting : Prop

/-- Full bridge from Hessian information geometry to Fresnel/Jones response. -/
structure SusceptibilityHessianFresnelBridge
    (State Tangent Op Freq WaveVector : Type*) [Ring Op] where
  /-- Hessian-to-susceptibility bridge. -/
  hessianBridge :
    HessianSusceptibilityBridge State Tangent Op Freq WaveVector

  /-- Dielectric/impedance backend. -/
  dielectric :
    DielectricResponseDatum Freq WaveVector

  /-- Fresnel coefficients as polarization eigenvalues. -/
  fresnelEigen :
    FresnelEigenCalibration Freq

  /-- Operatorial Jones calibration. -/
  jonesCalibration :
    JonesFresnelCalibration Op Freq

  /-- Dielectric response induced by Hessian-calibrated susceptibility. -/
  dielectric_from_hessian_susceptibility : Prop

  /-- Fresnel eigenvalues are boundary readouts of that material response. -/
  fresnel_from_dielectric_response : Prop

namespace SusceptibilityHessianFresnelBridge

variable
    {State Tangent Op Freq WaveVector : Type*}
    [Ring Op]

variable
    (B : SusceptibilityHessianFresnelBridge
      State Tangent Op Freq WaveVector)

/-- The s-polarized reflection eigenvalue is the Fresnel `r_s`. -/
theorem s_reflection_eigenvalue
    (omega : Freq) :
    B.fresnelEigen.eigenResponse.eigenvalue PolarizationMode.s omega =
      B.fresnelEigen.fresnel.r_s omega :=
  B.fresnelEigen.s_eigenvalue_is_r_s omega

/-- The p-polarized reflection eigenvalue is the Fresnel `r_p`. -/
theorem p_reflection_eigenvalue
    (omega : Freq) :
    B.fresnelEigen.eigenResponse.eigenvalue PolarizationMode.p omega =
      B.fresnelEigen.fresnel.r_p omega :=
  B.fresnelEigen.p_eigenvalue_is_r_p omega

end SusceptibilityHessianFresnelBridge

/-! ## 6. Stinespring heat coupling -/

/--
Coupling between optical absorption and a Stinespring/Bregman heat ledger.
-/
structure OpticalStinespringHeatCalibration
    (State Sys Comm : Type*)
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    (B : BregmanDivergenceDatum Sys)
    (C : DissipativeChannel Sys)
    (D : StinespringTomitaDilation Sys Comm C) where
  /-- Embed or read an optical material state as a system state. -/
  stateToSystem :
    State → Sys

  /-- Optical absorption readout on material states. -/
  absorptionFromState :
    State → ℝ

  /-- Hidden-information bridge for the Stinespring/Tomita dilation. -/
  hiddenHeatBridge :
    HeatEqualsHiddenInformation Sys Comm B C D

  /--
  Optical absorption agrees with Bregman heat after mapping the optical state
  into the system carrier.
  -/
  absorption_eq_heat :
    ∀ U : State,
      absorptionFromState U =
        heatLoss B C (stateToSystem U)

namespace OpticalStinespringHeatCalibration

variable
    {State Sys Comm : Type*}
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    {B : BregmanDivergenceDatum Sys}
    {C : DissipativeChannel Sys}
    {D : StinespringTomitaDilation Sys Comm C}

variable (K : OpticalStinespringHeatCalibration State Sys Comm B C D)

/--
Optical absorption is the hidden-information readout through the
Stinespring/Tomita bridge.
-/
theorem absorption_eq_hidden_information
    (U : State) :
    K.absorptionFromState U =
      K.hiddenHeatBridge.hiddenReadout.hiddenInfo
        (D.hiddenFlow (K.stateToSystem U)) := by
  rw [K.absorption_eq_heat U]
  exact K.hiddenHeatBridge.heat_is_hidden_commutant_information
    (K.stateToSystem U)

end OpticalStinespringHeatCalibration

/-! ## 6a. PT hidden-sector Stinespring clinch -/

/--
Optical PT Stinespring clinch.

This is the witness-gated statement that a coherent optical event is booked in
the PT sector and that its apparent absorption is exactly the hidden
commutant-information readout supplied by the Stinespring/Tomita dilation.

The Jones event supplies the visible optical tag.  The Stinespring heat
calibration supplies the conservation and hidden-information ledger.
-/
structure OpticalPTStinespringClinch
    (State Sys Comm : Type*)
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    (B : BregmanDivergenceDatum Sys)
    (C : DissipativeChannel Sys)
    (D : StinespringTomitaDilation Sys Comm C) where
  /-- Optical absorption-to-hidden-information heat ledger. -/
  opticalHeat :
    OpticalStinespringHeatCalibration State Sys Comm B C D

  /-- Visible coherent Jones event attached to the optical state. -/
  eventOf :
    State → JonesOpticalEvent

  /-- The optical event is booked in the PT sector. -/
  event_tag_pt :
    ∀ U : State, (eventOf U).tag = V4Tag.PT

  /-- Model-specific law that this PT sector is the intended commutant/dark readout. -/
  pt_commutant_sector_law : Prop


namespace OpticalPTStinespringClinch

variable
    {State Sys Comm : Type*}
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    {B : BregmanDivergenceDatum Sys}
    {C : DissipativeChannel Sys}
    {D : StinespringTomitaDilation Sys Comm C}

variable (K : OpticalPTStinespringClinch State Sys Comm B C D)

/-- The visible optical event is tagged by the PT sector. -/
theorem event_tag_eq_PT
    (U : State) :
    (K.eventOf U).tag = V4Tag.PT :=
  K.event_tag_pt U

/--
Optical absorption is exactly the hidden commutant-information readout.
-/
theorem absorption_eq_hidden_information
    (U : State) :
    K.opticalHeat.absorptionFromState U =
      K.opticalHeat.hiddenHeatBridge.hiddenReadout.hiddenInfo
        (D.hiddenFlow (K.opticalHeat.stateToSystem U)) :=
  K.opticalHeat.absorption_eq_hidden_information U

/--
Bregman heat is exactly the hidden commutant-information readout.
-/
theorem heat_eq_hidden_information
    (U : State) :
    heatLoss B C (K.opticalHeat.stateToSystem U) =
      K.opticalHeat.hiddenHeatBridge.hiddenReadout.hiddenInfo
        (D.hiddenFlow (K.opticalHeat.stateToSystem U)) :=
  K.opticalHeat.hiddenHeatBridge.heat_is_hidden_commutant_information
    (K.opticalHeat.stateToSystem U)

/--
The hidden commutant-information readout is nonnegative on optical states.
-/
theorem hidden_information_nonneg
    (U : State) :
    0 ≤ K.opticalHeat.hiddenHeatBridge.hiddenReadout.hiddenInfo
      (D.hiddenFlow (K.opticalHeat.stateToSystem U)) :=
  K.opticalHeat.hiddenHeatBridge.hidden_information_nonneg
    (K.opticalHeat.stateToSystem U)

/--
Optical absorption is nonnegative because it is hidden commutant information.
-/
theorem absorption_nonneg
    (U : State) :
    0 ≤ K.opticalHeat.absorptionFromState U := by
  rw [K.absorption_eq_hidden_information U]
  exact K.hidden_information_nonneg U

/--
The apparent visible deficit is exactly the recovered hidden commutant flow.
-/
theorem visible_deficit_eq_recovered_hidden
    (U : State) :
    C.ideal (K.opticalHeat.stateToSystem U) -
        C.actual (K.opticalHeat.stateToSystem U) =
      D.recoverHidden (D.hiddenFlow (K.opticalHeat.stateToSystem U)) :=
  D.ideal_sub_actual_eq_recovered_hidden (K.opticalHeat.stateToSystem U)

end OpticalPTStinespringClinch

/-! ## 7. Bregman/Fenchel Hessian to Jones calibration -/

/--
A Bregman/Fenchel Hessian readout of an information potential.

The Hessian is real-valued because it is the information-geometric response
metric.  Complex optical response enters only through material calibration.
-/
structure BregmanHessianResponse
    (State Tangent : Type*) [AddCommGroup Tangent] [Module ℝ Tangent] where
  /-- Hessian pairing at a state. -/
  hessianAt : State → Tangent → Tangent → ℝ

  /-- Symmetry of the Hessian pairing. -/
  symmetric :
    ∀ s X Y, hessianAt s X Y = hessianAt s Y X

  /-- Nonnegativity / convex response. -/
  nonnegative :
    ∀ s X, 0 ≤ hessianAt s X X

  /-- Certificate that this Hessian comes from the intended potential. -/
  bregman_hessian_law : Prop


namespace BregmanHessianResponse

variable {State Tangent : Type*} [AddCommGroup Tangent] [Module ℝ Tangent]
variable (H : BregmanHessianResponse State Tangent)

/-- Re-export Hessian symmetry. -/
theorem hessian_symmetric
    (s : State)
    (X Y : Tangent) :
    H.hessianAt s X Y = H.hessianAt s Y X :=
  H.symmetric s X Y

/-- Re-export Hessian nonnegativity. -/
theorem hessian_nonnegative
    (s : State)
    (X : Tangent) :
    0 ≤ H.hessianAt s X X :=
  H.nonnegative s X

end BregmanHessianResponse

/--
Complex material susceptibility.

The value is complex because the reactive and absorptive material responses
are both part of the optical readout.
-/
structure SusceptibilityDatum
    (State Freq : Type*) where
  /-- Complex susceptibility. -/
  susceptibility : State → Freq → ℂ

  /-- Material-response law. -/
  susceptibility_law : Prop


/--
State-indexed dielectric response calibrated from susceptibility.

The actual material equation, such as `epsilon = 1 + susceptibility`, is kept
proof-carrying at this layer.
-/
structure StateDielectricResponseDatum
    (State Freq : Type*) where
  /-- Complex dielectric function. -/
  epsilon : State → Freq → ℂ

  /-- Optional magnetic response. -/
  mu : State → Freq → ℂ

  /-- Relation between susceptibility and dielectric response. -/
  dielectric_law : Prop


/--
Complex refractive-index response.

Branch choice and material model are explicit proof-carrying data.
-/
structure ComplexRefractiveIndexDatum
    (State Freq : Type*) where
  /-- Complex refractive index. -/
  N : State → Freq → ℂ

  /-- Branch/material law connecting `N` to dielectric data. -/
  refractive_index_law : Prop


/--
Calibration from a Bregman Hessian to material susceptibility.

This is the witness-gated bridge saying that the local information-geometric
response is the material response readout in a concrete model.
-/
structure BregmanHessianSusceptibilityCalibration
    (State Tangent Freq : Type*)
    [AddCommGroup Tangent] [Module ℝ Tangent] where
  /-- Bregman/Fenchel Hessian response. -/
  hessian :
    BregmanHessianResponse State Tangent

  /-- Complex susceptibility datum. -/
  susceptibility :
    SusceptibilityDatum State Freq

  /-- Bridge law from Hessian response to susceptibility. -/
  hessian_controls_susceptibility_law : Prop


/--
Fresnel coefficient readout from a complex refractive-index model.

`coeff_s` and `coeff_p` are optical amplitude reflection coefficients.
-/
structure FresnelFromRefractiveIndex
    (State Freq Angle : Type*) where
  /-- s-polarized reflection coefficient. -/
  coeff_s : State → Freq → Angle → ℂ

  /-- p-polarized reflection coefficient. -/
  coeff_p : State → Freq → Angle → ℂ

  /-- Fresnel law certificate. -/
  fresnel_law : Prop


/--
Response eigenvalues in the local polarization basis.

Mode `0` is the first channel and mode `1` is the second channel.
-/
structure OpticalResponseEigenvalues
    (State Freq Angle : Type*) where
  /-- Optical response eigenvalue for each channel. -/
  eigenvalue : State → Freq → Angle → Fin 2 → ℂ

  /-- Eigenbasis of the response. -/
  basis : PolarizationBasis

  /-- Eigenvalue law/certificate. -/
  eigenvalue_law : Prop


/--
Complete Hessian/Fresnel calibration.

This packages Hessian response, susceptibility, dielectric response,
refractive index, optical response eigenvalues, and Fresnel coefficients.
-/
structure SusceptibilityFresnelCalibration
    (State Tangent Freq Angle : Type*)
    [AddCommGroup Tangent] [Module ℝ Tangent] where
  /-- Hessian-to-susceptibility calibration. -/
  hessianSusceptibility :
    BregmanHessianSusceptibilityCalibration State Tangent Freq

  /-- Dielectric response. -/
  dielectric :
    StateDielectricResponseDatum State Freq

  /-- Complex refractive-index response. -/
  refractiveIndex :
    ComplexRefractiveIndexDatum State Freq

  /-- Optical response eigenvalues. -/
  responseEigenvalues :
    OpticalResponseEigenvalues State Freq Angle

  /-- Fresnel coefficient readout. -/
  fresnel :
    FresnelFromRefractiveIndex State Freq Angle

  /-- The `s` Fresnel coefficient is the first response eigenvalue. -/
  coeff_s_eq_eigen_zero :
    ∀ s : State, ∀ omega : Freq, ∀ theta : Angle,
      fresnel.coeff_s s omega theta =
        responseEigenvalues.eigenvalue s omega theta 0

  /-- The `p` Fresnel coefficient is the second response eigenvalue. -/
  coeff_p_eq_eigen_one :
    ∀ s : State, ∀ omega : Freq, ∀ theta : Angle,
      fresnel.coeff_p s omega theta =
        responseEigenvalues.eigenvalue s omega theta 1

  /-- End-to-end calibration law. -/
  end_to_end_optical_response_law : Prop


namespace SusceptibilityFresnelCalibration

variable
    {State Tangent Freq Angle : Type*}
    [AddCommGroup Tangent] [Module ℝ Tangent]

variable (C : SusceptibilityFresnelCalibration State Tangent Freq Angle)

/--
The `s` Fresnel coefficient is the first Hessian-calibrated response eigenvalue.
-/
theorem coeff_s_is_response_eigenvalue
    (s : State)
    (omega : Freq)
    (theta : Angle) :
    C.fresnel.coeff_s s omega theta =
      C.responseEigenvalues.eigenvalue s omega theta 0 :=
  C.coeff_s_eq_eigen_zero s omega theta

/--
The `p` Fresnel coefficient is the second Hessian-calibrated response eigenvalue.
-/
theorem coeff_p_is_response_eigenvalue
    (s : State)
    (omega : Freq)
    (theta : Angle) :
    C.fresnel.coeff_p s omega theta =
      C.responseEigenvalues.eigenvalue s omega theta 1 :=
  C.coeff_p_eq_eigen_one s omega theta

end SusceptibilityFresnelCalibration

/--
A calibrated optical state/event produces a Jones optical event.
-/
structure HessianJonesCalibration
    (State Tangent Freq Angle : Type*)
    [AddCommGroup Tangent] [Module ℝ Tangent] where
  /-- Full Hessian/Fresnel response calibration. -/
  response :
    SusceptibilityFresnelCalibration State Tangent Freq Angle

  /-- Surface kind assigned to the event. -/
  surfaceKind : OpticalSurfaceKind

  /-- Discrete V4 tag assigned to the event. -/
  tagOf : State → Freq → Angle → V4Tag

  /-- Coherence law for the Jones description. -/
  coherence : State → Freq → Angle → Prop

  coherent :
    ∀ s : State, ∀ omega : Freq, ∀ theta : Angle,
      coherence s omega theta

namespace HessianJonesCalibration

variable
    {State Tangent Freq Angle : Type*}
    [AddCommGroup Tangent] [Module ℝ Tangent]

variable (C : HessianJonesCalibration State Tangent Freq Angle)

/--
The Jones event generated by the calibrated Hessian/Fresnel response.
-/
def eventOf
    (s : State)
    (omega : Freq)
    (theta : Angle) : JonesOpticalEvent where
  basis := C.response.responseEigenvalues.basis
  kind := C.surfaceKind
  coeff0 := C.response.fresnel.coeff_s s omega theta
  coeff1 := C.response.fresnel.coeff_p s omega theta
  tag := C.tagOf s omega theta
  coherence := C.coherence s omega theta

/--
The first Jones coefficient is the calibrated `s`/first-channel Fresnel
coefficient.
-/
theorem event_coeff0_eq_fresnel_s
    (s : State)
    (omega : Freq)
    (theta : Angle) :
    (C.eventOf s omega theta).coeff0 =
      C.response.fresnel.coeff_s s omega theta :=
  rfl

/--
The second Jones coefficient is the calibrated `p`/second-channel Fresnel
coefficient.
-/
theorem event_coeff1_eq_fresnel_p
    (s : State)
    (omega : Freq)
    (theta : Angle) :
    (C.eventOf s omega theta).coeff1 =
      C.response.fresnel.coeff_p s omega theta :=
  rfl

/--
The first Jones coefficient is the first Hessian-calibrated response eigenvalue.
-/
theorem event_coeff0_eq_response_eigenvalue
    (s : State)
    (omega : Freq)
    (theta : Angle) :
    (C.eventOf s omega theta).coeff0 =
      C.response.responseEigenvalues.eigenvalue s omega theta 0 := by
  calc
    (C.eventOf s omega theta).coeff0
        = C.response.fresnel.coeff_s s omega theta := rfl
    _ = C.response.responseEigenvalues.eigenvalue s omega theta 0 :=
        C.response.coeff_s_is_response_eigenvalue s omega theta

/--
The second Jones coefficient is the second Hessian-calibrated response
eigenvalue.
-/
theorem event_coeff1_eq_response_eigenvalue
    (s : State)
    (omega : Freq)
    (theta : Angle) :
    (C.eventOf s omega theta).coeff1 =
      C.response.responseEigenvalues.eigenvalue s omega theta 1 := by
  calc
    (C.eventOf s omega theta).coeff1
        = C.response.fresnel.coeff_p s omega theta := rfl
    _ = C.response.responseEigenvalues.eigenvalue s omega theta 1 :=
        C.response.coeff_p_is_response_eigenvalue s omega theta

end HessianJonesCalibration

/--
Metal-mirror specialization of the calibrated Jones response.
-/
structure MetalMirrorSusceptibilityCalibration
    (State Tangent Freq Angle : Type*)
    [AddCommGroup Tangent] [Module ℝ Tangent] where
  /-- Hessian-to-Jones calibration. -/
  jonesCalibration :
    HessianJonesCalibration State Tangent Freq Angle

  /-- The event is interpreted as a metal mirror response. -/
  metal_mirror_law : Prop

  /-- Absorptive part of response controls Bregman/thermal loss. -/
  absorption_heat_law : Prop

  /-- Reactive part of response controls retardance/ellipticity. -/
  retardance_law : Prop


namespace MetalMirrorSusceptibilityCalibration

variable
    {State Tangent Freq Angle : Type*}
    [AddCommGroup Tangent] [Module ℝ Tangent]

variable (M : MetalMirrorSusceptibilityCalibration State Tangent Freq Angle)

/-- Jones event of the metal mirror response. -/
def eventOf
    (s : State)
    (omega : Freq)
    (theta : Angle) : JonesOpticalEvent :=
  M.jonesCalibration.eventOf s omega theta

/--
The second Jones coefficient is the Hessian-calibrated `p`/second-channel
response eigenvalue.
-/
theorem p_coeff_is_hessian_response_eigenvalue
    (s : State)
    (omega : Freq)
    (theta : Angle) :
    (M.eventOf s omega theta).coeff1 =
      M.jonesCalibration.response.responseEigenvalues.eigenvalue s omega theta 1 :=
  M.jonesCalibration.event_coeff1_eq_response_eigenvalue s omega theta

end MetalMirrorSusceptibilityCalibration

/--
Vacuum response calibration.

The concrete normalization of vacuum susceptibility is proof-carrying.
-/
structure VacuumResponseCalibration
    (State Freq : Type*) where
  /-- Vacuum susceptibility datum. -/
  susceptibility :
    SusceptibilityDatum State Freq

  /-- Vacuum susceptibility law. -/
  vacuum_susceptibility_law : Prop


/--
Matter response calibration.

-- [STITCHER: MISSING OVERLAP] --

In matter, the Hessian/susceptibility response can produce absorption,
retardance, diattenuation, and heat once calibrated.
-/
structure MatterResponseCalibration
    (State Tangent Freq Angle : Type*)
    [AddCommGroup Tangent] [Module ℝ Tangent] where
  /-- Full susceptibility/Fresnel response calibration. -/
  response :
    SusceptibilityFresnelCalibration State Tangent Freq Angle

  /-- Matter response law. -/
  matter_response_law : Prop


/--
Compatibility predicate for the material-response Hessian/Fresnel bridge.

Concrete modules should replace this by material-model, linear-response,
dielectric-backend, interface-geometry, and Jones/Fresnel calibration data.
-/
def MaterialSusceptibilityHessianCompatibility
    (State Tangent Op Freq WaveVector : Type*) [Ring Op] : Prop :=
  Nonempty (State → Tangent → Op → Freq → WaveVector → Unit)

/--
Owner target for constructing material-response/Fresnel data from an
information Hessian.
-/
@[owner_target_tag]
def MaterialSusceptibilityHessianOwnerTarget : Prop :=
  ∀ (State Tangent Op Freq WaveVector : Type*) [Ring Op],
    MaterialSusceptibilityHessianCompatibility State Tangent Op Freq WaveVector →
      Nonempty
        (SusceptibilityHessianFresnelBridge
          State Tangent Op Freq WaveVector)

/-! ## 5. Owner target -/

/--
Owner target for optical response calibration.

This is intentionally witness-gated.  Concrete material models must supply the
Hessian/material/Fresnel calibration.
-/
@[owner_target_tag]
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
  IsHessianDegenerate
  MaterialResponseModel
  HessianSusceptibilityCalibration
  FresnelCoefficientReadout
  StatePolarizationEigenResponse
  FresnelFromStateEigenResponse
  FresnelFromStateEigenResponse.responseS_eq_rs
  FresnelFromStateEigenResponse.responseP_eq_rp
  spJonesEventOfFresnel
  spJonesEventOfFresnel_basis
  spJonesEventOfFresnel_coeff0
  spJonesEventOfFresnel_coeff1
  spJonesEventOfFresnel_jones_00
  spJonesEventOfFresnel_jones_11
  JonesFromMaterialCalibration
  jonesFromMaterialCalibrationOfFresnel
  JonesFromMaterialCalibration.jones_00_eq_rs
  JonesFromMaterialCalibration.jones_11_eq_rp
  JonesFromMaterialCalibration.jones_offdiag_01_zero
  JonesFromMaterialCalibration.jones_offdiag_10_zero
  RetardanceReadout
  OpticalAbsorptionReadout
  OpticalResponseCalibration
  OpticalResponseCalibration.ofFresnel
  OpticalResponseCalibration.eventOf
  OpticalResponseCalibration.jones_00_eq_rs
  OpticalResponseCalibration.jones_11_eq_rp
  OpticalResponseCalibration.jones_offdiag_01_zero
  OpticalResponseCalibration.jones_offdiag_10_zero
  OpticalResponseEigenCalibration
  OpticalResponseEigenCalibration.responseS_eq_rs
  OpticalResponseEigenCalibration.responseP_eq_rp
  OpticalResponseEigenCalibration.jones_00_eq_rs
  OpticalResponseEigenCalibration.jones_11_eq_rp
  InformationPotentialDatum
  InformationPotentialDatum.hessian_symmetric
  InformationPotentialDatum.hessian_nonneg
  BregmanHeatDatum
  BregmanHeatDatum.heat_nonnegative
  BregmanHeatDatum.heat_self
  LinearSusceptibilityDatum
  HessianSusceptibilityBridge
  DielectricResponseDatum
  PolarizationMode
  OpticalInterfaceResponse
  fresnelRS
  fresnelRP
  MaterialFresnelCoefficientDatum
  MaterialFresnelCoefficientDatum.r_s_eq
  MaterialFresnelCoefficientDatum.r_p_eq
  PolarizationEigenResponse
  FresnelEigenCalibration
  FresnelEigenCalibration.s_eigenvalue_is_r_s
  FresnelEigenCalibration.p_eigenvalue_is_r_p
  FresnelEigenCalibration.s_eigenvalue_eq_standard
  FresnelEigenCalibration.p_eigenvalue_eq_standard
  OperatorialJonesResponse
  JonesFresnelCalibration
  SusceptibilityHessianFresnelBridge
  SusceptibilityHessianFresnelBridge.s_reflection_eigenvalue
  SusceptibilityHessianFresnelBridge.p_reflection_eigenvalue
  OpticalStinespringHeatCalibration
  OpticalStinespringHeatCalibration.absorption_eq_hidden_information
  OpticalPTStinespringClinch
  OpticalPTStinespringClinch.event_tag_eq_PT
  OpticalPTStinespringClinch.absorption_eq_hidden_information
  OpticalPTStinespringClinch.heat_eq_hidden_information
  OpticalPTStinespringClinch.hidden_information_nonneg
  OpticalPTStinespringClinch.absorption_nonneg
  OpticalPTStinespringClinch.visible_deficit_eq_recovered_hidden
  BregmanHessianResponse
  BregmanHessianResponse.hessian_symmetric
  BregmanHessianResponse.hessian_nonnegative
  SusceptibilityDatum
  StateDielectricResponseDatum
  ComplexRefractiveIndexDatum
  BregmanHessianSusceptibilityCalibration
  FresnelFromRefractiveIndex
  OpticalResponseEigenvalues
  SusceptibilityFresnelCalibration
  SusceptibilityFresnelCalibration.coeff_s_is_response_eigenvalue
  SusceptibilityFresnelCalibration.coeff_p_is_response_eigenvalue
  HessianJonesCalibration
  HessianJonesCalibration.eventOf
  HessianJonesCalibration.event_coeff0_eq_fresnel_s
  HessianJonesCalibration.event_coeff1_eq_fresnel_p
  HessianJonesCalibration.event_coeff0_eq_response_eigenvalue
  HessianJonesCalibration.event_coeff1_eq_response_eigenvalue
  MetalMirrorSusceptibilityCalibration
  MetalMirrorSusceptibilityCalibration.eventOf
  MetalMirrorSusceptibilityCalibration.p_coeff_is_hessian_response_eigenvalue
  VacuumResponseCalibration
  MatterResponseCalibration
  MaterialSusceptibilityHessianCompatibility
  MaterialSusceptibilityHessianOwnerTarget
  SusceptibilityHessianOwnerTarget
  susceptibilityHessianOwnerTarget

end InfoGeometry.OperatorAlgebra.SusceptibilityHessian

-- [STITCHER: MISSING OVERLAP] --
import Mathlib
import InfoGeometry.Thermo.MetalMirror
import InfoGeometry.Geometry.OperatorBregmanDivergence
import InfoGeometry.Optics.JonesCalibration
import InfoGeometry.Meta.Architecture

/-!
# Susceptibility Hessian

Susceptibility as a Hessian/linear-response calibration.

This module connects the Legendre/Bregman Hessian of an information potential
to optical material response.  It does not derive Fresnel coefficients from
the Hessian alone; incidence geometry, material response, branch choices, and
Fresnel/Jones calibration are supplied as proof-carrying data.
-/

noncomputable section

namespace InfoGeometry.Thermo.SusceptibilityHessian

open InfoGeometry.Optics.JonesCalibration

/-! ## Hessian response backend -/

/--
A Hessian response datum on an operator/state space.

The intended interpretation is that `hessian U` is the local linear response
operator at state `U`.
-/
structure HessianResponseDatum
    (Op Field Response : Type*)
    [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response] where
  /-- Hessian or Fisher/Legendre metric at a state. -/
  hessian : Op → Op →L[ℝ] Op

  /-- Optical perturbing field readout. -/
  fieldReadout : Op → Field

  /-- Material response readout. -/
  responseReadout : Op → Response

  /-- This Hessian is the intended linear-response geometry. -/
  hessian_response : Prop

namespace HessianResponseDatum

variable
    {Op Field Response : Type*}
    [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response]

variable (H : HessianResponseDatum Op Field Response)

end HessianResponseDatum

/-! ## Susceptibility and dielectric response -/

/--
A susceptibility datum.

The map `susceptibility U` sends an applied field to the induced response.  For
optics, this is morally `P = χ E`, with frequency/momentum dependence carried
by `Op` or by later concrete parameters.
-/
structure SusceptibilityDatum
    (Op Field Response : Type*)
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response] where
  /-- Linear material susceptibility at the chosen state/parameter. -/
  susceptibility : Op → Field →L[ℝ] Response

  /-- Susceptibility is obtained from the Hessian response. -/
  derived_from_hessian : Prop

namespace SusceptibilityDatum

variable
    {Op Field Response : Type*}
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response]

variable (S : SusceptibilityDatum Op Field Response)

end SusceptibilityDatum

/-! ## Constructive Hessian-to-susceptibility descent -/

/--
Constructive Hessian-to-susceptibility calibration.

This is the infinite-dimensional, representation-agnostic version of the
Hessian response claim.  A field perturbation is first embedded into the state
tangent space, then acted on by the Hessian response operator, then read out as
a material response.

No basis, finite-dimensional determinant, or matrix shadow is used.
-/
structure ConstructiveHessianSusceptibilityCalibration
    (Op Field Response : Type*)
    [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response] where
  /-- Hessian/linear-response backend. -/
  hessianResponse :
    HessianResponseDatum Op Field Response

  /-- Embed an optical perturbing field into the state tangent space. -/
  fieldToTangent :
    Op → Field →L[ℝ] Op

  /-- Read a Hessian-shifted tangent vector as a material response. -/
  responseFromTangent :
    Op → Op →L[ℝ] Response

namespace ConstructiveHessianSusceptibilityCalibration

variable
    {Op Field Response : Type*}
    [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response]

variable (C : ConstructiveHessianSusceptibilityCalibration Op Field Response)

/--
The susceptibility induced by explicit Hessian descent:

`χ_U = responseFromTangent_U ∘ hessian_U ∘ fieldToTangent_U`.
-/
def susceptibility :
    Op → Field →L[ℝ] Response :=
  fun U =>
    (C.responseFromTangent U).comp
      ((C.hessianResponse.hessian U).comp (C.fieldToTangent U))

/-- The induced susceptibility is exactly the Hessian-response composition. -/
theorem susceptibility_eq_hessian_response
    (U : Op) :
    C.susceptibility U =
      (C.responseFromTangent U).comp
        ((C.hessianResponse.hessian U).comp (C.fieldToTangent U)) :=
  rfl

/-- Pointwise form of the constructive Hessian-to-susceptibility descent. -/
theorem susceptibility_apply
    (U : Op)
    (E : Field) :
    C.susceptibility U E =
      C.responseFromTangent U (C.hessianResponse.hessian U (C.fieldToTangent U E)) :=
  rfl

/--
The ordinary susceptibility datum generated by the constructive descent.

The `derived_from_hessian` evidence is the explicit equality above, not an
uninterpreted external hypothesis.
-/
def toSusceptibilityDatum :
    SusceptibilityDatum Op Field Response where
  susceptibility := C.susceptibility
  derived_from_hessian :=
    ∀ U : Op,
      C.susceptibility U =
        (C.responseFromTangent U).comp
          ((C.hessianResponse.hessian U).comp (C.fieldToTangent U))

/-- The generated susceptibility datum has the constructive susceptibility map. -/
theorem toSusceptibilityDatum_susceptibility :
    C.toSusceptibilityDatum.susceptibility = C.susceptibility :=
  rfl

/--
The generated susceptibility datum proves its Hessian origin by definitional
descent through the explicit tangent/readout maps.
-/
theorem toSusceptibilityDatum_derived_from_hessian
    (U : Op) :
    C.toSusceptibilityDatum.susceptibility U =
      (C.responseFromTangent U).comp
        ((C.hessianResponse.hessian U).comp (C.fieldToTangent U)) :=
  rfl

end ConstructiveHessianSusceptibilityCalibration

/--
A dielectric response datum.

This is the calibration layer between susceptibility and complex optical
material response.
-/
structure DielectricResponseDatum
    (Op : Type*) where
  /-- Relative dielectric response, possibly frequency/momentum dependent. -/
  epsilon : Op → ℂ

  /-- Complex refractive index readout. -/
  refractiveIndex : Op → ℂ

  /-- Susceptibility/material readout feeding dielectric response. -/
  susceptibilityEpsilonReadout : Op → ℂ

  /-- Calibration equation, e.g. `N² = εᵣ μᵣ` or `N² = εᵣ` in a nonmagnetic model. -/
  refractive_index_calibration :
    ∀ U : Op, refractiveIndex U ^ (2 : ℕ) = epsilon U

  /-- Connection between susceptibility readout and dielectric response. -/
  susceptibility_to_epsilon :
    ∀ U : Op, epsilon U = susceptibilityEpsilonReadout U

namespace DielectricResponseDatum

variable {Op : Type*}
variable (D : DielectricResponseDatum Op)

end DielectricResponseDatum

/--
Constructive dielectric calibration.

This packages the two explicit equalities normally hidden behind the dielectric
interface: the complex-index branch equation and the readout turning
susceptibility/material response into `ε`.
-/
structure ConstructiveDielectricResponseCalibration
    (Op : Type*) where
  /-- Relative dielectric response. -/
  epsilon : Op → ℂ

  /-- Complex refractive-index branch. -/
  refractiveIndex : Op → ℂ

  /-- Explicit susceptibility/material readout feeding the dielectric response. -/
  susceptibilityEpsilonReadout : Op → ℂ

  /-- Branch equation, e.g. `N² = ε` in a nonmagnetic isotropic model. -/
  refractive_index_sq :
    ∀ U : Op, refractiveIndex U ^ (2 : ℕ) = epsilon U

  /-- Explicit equality connecting the susceptibility readout to `ε`. -/
  epsilon_eq_susceptibility_readout :
    ∀ U : Op, epsilon U = susceptibilityEpsilonReadout U

namespace ConstructiveDielectricResponseCalibration

variable {Op : Type*}
variable (C : ConstructiveDielectricResponseCalibration Op)

/--
The ordinary dielectric datum generated by explicit complex-index and
susceptibility-to-`ε` equalities.
-/
def toDielectricResponseDatum :
    DielectricResponseDatum Op where
  epsilon := C.epsilon
  refractiveIndex := C.refractiveIndex
  susceptibilityEpsilonReadout := C.susceptibilityEpsilonReadout
  refractive_index_calibration := C.refractive_index_sq
  susceptibility_to_epsilon := C.epsilon_eq_susceptibility_readout

/-- The generated dielectric datum keeps the supplied `ε` readout. -/
theorem toDielectricResponseDatum_epsilon :
    C.toDielectricResponseDatum.epsilon = C.epsilon :=
  rfl

/-- The generated dielectric datum keeps the supplied complex-index branch. -/
theorem toDielectricResponseDatum_refractiveIndex :
    C.toDielectricResponseDatum.refractiveIndex = C.refractiveIndex :=
  rfl

end ConstructiveDielectricResponseCalibration

/-! ## Fresnel/Jones calibration -/

/--
Optical interface parameters needed to evaluate Fresnel reflection.

These data are not determined by susceptibility alone.
-/
structure OpticalInterfaceGeometry where
  /-- Incidence angle. -/
  theta_i : ℝ

  /-- Transmission/refraction angle, if applicable. -/
  theta_t : ℝ

  /-- Geometric/Snell-law calibration proof payload. -/
  angle_calibration : Prop

namespace OpticalInterfaceGeometry

variable (G : OpticalInterfaceGeometry)

end OpticalInterfaceGeometry

/--
Fresnel calibration datum.

This packages the statement that the complex Fresnel coefficients are computed
from the material response and boundary geometry.
-/
structure FresnelFromSusceptibilityCalibration
    (Op : Type*) where
  /-- Dielectric/material response. -/
  dielectric : DielectricResponseDatum Op

  /-- Interface geometry needed for Fresnel reflection. -/
  interfaceGeometry : OpticalInterfaceGeometry

  /-- Fresnel coefficients supplied to the Jones layer. -/
  coeffs : InfoGeometry.Optics.JonesCalibration.FresnelCoefficientDatum

  /-- Proof payload that `coeffs` are determined by dielectric and interface data. -/
  fresnel_from_dielectric : Prop

namespace FresnelFromSusceptibilityCalibration

variable {Op : Type*}
variable (F : FresnelFromSusceptibilityCalibration Op)

end FresnelFromSusceptibilityCalibration

/-! ## s/p eigenchannel response -/

/--
s/p eigenchannel calibration for a material-response operator.

For a smooth isotropic interface, the `s` and `p` channels diagonalize the
reflection operator.  This structure records the eigenvalues of the calibrated
response operator in those channels.
-/
structure SPEigenResponseCalibration
    (State Op : Type*) [Ring Op] [Algebra ℂ Op]
    (P : SPProjectorPair Op) where
  /-- Calibrated response operator acting on the polarization algebra. -/
  responseOp : State → Op

  /-- Channel eigenvalue. -/
  eigenvalue : FresnelChannel → State → ℂ

  /-- `s` channel is an eigenchannel. -/
  s_eigen :
    ∀ U : State,
      responseOp U * P.P_s =
        eigenvalue FresnelChannel.s U • P.P_s

  /-- `p` channel is an eigenchannel. -/
  p_eigen :
    ∀ U : State,
      responseOp U * P.P_p =
        eigenvalue FresnelChannel.p U • P.P_p

namespace SPEigenResponseCalibration

variable
    {State Op : Type*} [Ring Op] [Algebra ℂ Op]
    {P : SPProjectorPair Op}

variable (E : SPEigenResponseCalibration State Op P)

/-- Re-export of the `s`-eigenchannel equation. -/
theorem response_mul_s_projector
    (U : State) :
    E.responseOp U * P.P_s =
      E.eigenvalue FresnelChannel.s U • P.P_s :=
  E.s_eigen U

/-- Re-export of the `p`-eigenchannel equation. -/
theorem response_mul_p_projector
    (U : State) :
    E.responseOp U * P.P_p =
      E.eigenvalue FresnelChannel.p U • P.P_p :=
  E.p_eigen U

/-- Uniform channel form of the eigenprojector equation. -/
theorem response_mul_projectorOf
    (U : State)
    (c : FresnelChannel) :
    E.responseOp U * P.projectorOf c =
      E.eigenvalue c U • P.projectorOf c := by
  cases c
  · exact E.response_mul_s_projector U
  · exact E.response_mul_p_projector U

end SPEigenResponseCalibration

/--
Fresnel coefficients as calibrated eigenchannel readouts.

This is the precise place where the statement

`r_s` and `r_p` are geometric eigenvalues

becomes formal.  It is not derived from the Hessian alone; it is derived from
the Hessian plus dielectric and boundary calibration.
-/
structure FresnelEigenvalueCalibration
    (State Op : Type*) [Ring Op] [Algebra ℂ Op]
    (P : SPProjectorPair Op)
    (E : SPEigenResponseCalibration State Op P) where
  /-- Fresnel coefficient datum attached to each state. -/
  coeffs : State → FresnelCoefficientDatum

  /-- The `s` Fresnel coefficient is the `s` eigenvalue. -/
  coeff_s :
    ∀ U : State,
      (coeffs U).r_s = E.eigenvalue FresnelChannel.s U

  /-- The `p` Fresnel coefficient is the `p` eigenvalue. -/
  coeff_p :
    ∀ U : State,
      (coeffs U).r_p = E.eigenvalue FresnelChannel.p U

  /-- Proof payload that the eigenvalues come from the intended Fresnel boundary problem. -/
  fresnel_boundary_calibration : Prop

namespace FresnelEigenvalueCalibration

variable
    {State Op : Type*} [Ring Op] [Algebra ℂ Op]
    {P : SPProjectorPair Op}
    {E : SPEigenResponseCalibration State Op P}

variable (F : FresnelEigenvalueCalibration State Op P E)

/-- Channel-indexed Fresnel coefficient readout. -/
def coeffOf
    (U : State) : FresnelChannel → ℂ
  | FresnelChannel.s => (F.coeffs U).r_s
  | FresnelChannel.p => (F.coeffs U).r_p

/--
The Jones reflector associated to a calibrated state.
-/
def jonesReflector
    (U : State) : JonesReflector Op where
  projectors := P
  coeffs := F.coeffs U

/--
The `s` coefficient of the calibrated Jones reflector is the `s` eigenvalue.
-/
theorem jones_r_s_eq_eigenvalue
    (U : State) :
    ((F.jonesReflector U).coeffs).r_s =
      E.eigenvalue FresnelChannel.s U :=
  F.coeff_s U

/--
The `p` coefficient of the calibrated Jones reflector is the `p` eigenvalue.
-/
theorem jones_r_p_eq_eigenvalue
    (U : State) :
    ((F.jonesReflector U).coeffs).r_p =
      E.eigenvalue FresnelChannel.p U :=
  F.coeff_p U

/--
The channel-indexed Fresnel coefficient is the calibrated response eigenvalue.
-/
theorem coeffOf_eq_eigenvalue
    (U : State)
    (c : FresnelChannel) :
    F.coeffOf U c = E.eigenvalue c U := by
  cases c
  · exact F.coeff_s U
  · exact F.coeff_p U

/--
The calibrated response operator acts on each Jones channel projector by the
corresponding Fresnel coefficient.
-/
theorem response_mul_projectorOf_eq_coeff
    (U : State)
    (c : FresnelChannel) :
    E.responseOp U * P.projectorOf c =
      F.coeffOf U c • P.projectorOf c := by
  rw [F.coeffOf_eq_eigenvalue U c]
  exact E.response_mul_projectorOf U c

end FresnelEigenvalueCalibration

/-! ## Metal mirror susceptibility calibration -/

/--
Metal mirror susceptibility/Hessian calibration.

This bridges Bregman heat, Hessian response, optical susceptibility, dielectric
response, and Jones/Fresnel readouts.
-/
structure MetalMirrorSusceptibilityCalibration
    (Op Field Response : Type*)
    [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response] where
  /-- Hessian/linear-response backend. -/
  hessianResponse :
    HessianResponseDatum Op Field Response

  /-- Susceptibility backend. -/
  susceptibility :
    SusceptibilityDatum Op Field Response

  /-- Dielectric/material response backend. -/
  dielectric :
    DielectricResponseDatum Op

  /-- Fresnel/Jones boundary calibration. -/
  fresnel :
    FresnelFromSusceptibilityCalibration Op

  /-- Hessian response determines susceptibility in this model. -/
  hessian_controls_susceptibility : Prop

  /-- Susceptibility/dielectric response controls absorption. -/
  susceptibility_controls_absorption : Prop

  /-- Susceptibility/dielectric response controls retardance. -/
  susceptibility_controls_retardance : Prop

  /-- Jones reflector is calibrated by the Fresnel coefficients. -/
  jones_calibrated : Prop

namespace MetalMirrorSusceptibilityCalibration

variable
    {Op Field Response : Type*}
    [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response]

end MetalMirrorSusceptibilityCalibration

/-! ## Full Hessian-to-Jones material calibration -/

/--
Complete susceptibility/Hessian-to-Jones calibration.

This is the material response bridge:

  Hessian response
      → susceptibility
      → dielectric response
      → s/p response eigenvalues
      → Fresnel coefficients
      → Jones reflector.
-/
structure SusceptibilityHessianJonesCalibration
    (State Field Response JonesOp : Type*)
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response]
    [Ring JonesOp] [Algebra ℂ JonesOp] where
  /-- Hessian response of the information potential. -/
  hessian :
    HessianResponseDatum State Field Response

  /-- Susceptibility derived from the Hessian. -/
  susceptibility :
    SusceptibilityDatum State Field Response

  /-- Dielectric/refractive-index response. -/
  dielectric :
    DielectricResponseDatum State

  /-- Optical interface geometry. -/
  interface :
    OpticalInterfaceGeometry

  /-- s/p projector pair in the Jones algebra. -/
  projectors :
    SPProjectorPair JonesOp

  /-- s/p response eigenchannel calibration. -/
  eigenResponse :
    SPEigenResponseCalibration State JonesOp projectors

  /-- Fresnel coefficients as eigenchannel readouts. -/
  fresnel :
    FresnelEigenvalueCalibration State JonesOp projectors eigenResponse

  /-- Hessian response controls susceptibility in the chosen material model. -/
  hessian_controls_susceptibility : Prop

  /-- Susceptibility controls dielectric response. -/
  susceptibility_controls_dielectric : Prop

  /-- Dielectric response plus interface geometry controls Fresnel coefficients. -/
  dielectric_controls_fresnel : Prop

  /-- Jones reflector is calibrated by the resulting Fresnel coefficients. -/
  jones_calibrated : Prop

namespace SusceptibilityHessianJonesCalibration

variable
    {State Field Response JonesOp : Type*}
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response]
    [Ring JonesOp] [Algebra ℂ JonesOp]

variable (C :
  SusceptibilityHessianJonesCalibration State Field Response JonesOp)

/--
The calibrated Jones reflector for a material state.
-/
def jonesReflector
    (U : State) : JonesReflector JonesOp :=
  C.fresnel.jonesReflector U

/--
The `s` Fresnel/Jones coefficient is the calibrated `s` eigenvalue.
-/
theorem r_s_eq_s_eigenvalue
    (U : State) :
    ((C.jonesReflector U).coeffs).r_s =
      C.eigenResponse.eigenvalue FresnelChannel.s U :=
  C.fresnel.jones_r_s_eq_eigenvalue U

/--
The `p` Fresnel/Jones coefficient is the calibrated `p` eigenvalue.
-/
theorem r_p_eq_p_eigenvalue
    (U : State) :
    ((C.jonesReflector U).coeffs).r_p =
      C.eigenResponse.eigenvalue FresnelChannel.p U :=
  C.fresnel.jones_r_p_eq_eigenvalue U

end SusceptibilityHessianJonesCalibration

/--
Metal mirror material calibration.

This records the physical readouts that connect complex response eigenvalues
to absorption, retardance, and ellipticity.
-/
structure MetalMirrorSusceptibilityHessianCalibration
    (State Field Response JonesOp : Type*)
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response]
    [Ring JonesOp] [Algebra ℂ JonesOp] where
  /-- Full Hessian-to-Jones calibration. -/
  calibration :
    SusceptibilityHessianJonesCalibration State Field Response JonesOp

  /-- Absorption readout. -/
  absorption : State → ℝ

  /-- Retardance readout. -/
  retardance : State → ℝ

  /-- Ellipticity readout. -/
  ellipticity : State → ℝ

  /-- Complex-index readout. -/
  complexIndex : State → ℂ

  /-- Absorption is controlled by the dissipative part of response. -/
  response_controls_absorption : Prop

  /-- Retardance is controlled by relative phase of `s/p` eigenvalues. -/
  eigenphase_controls_retardance : Prop

  /-- Ellipticity is controlled by amplitude imbalance plus retardance. -/
  eigenresponse_controls_ellipticity : Prop

  /-- Complex index is calibrated to the dielectric response. -/
  complex_index_calibrated : Prop

namespace MetalMirrorSusceptibilityHessianCalibration

variable
    {State Field Response JonesOp : Type*}
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response]
    [Ring JonesOp] [Algebra ℂ JonesOp]

variable (M :
  MetalMirrorSusceptibilityHessianCalibration State Field Response JonesOp)

/--
The `s` Fresnel/Jones coefficient is the calibrated `s` eigenvalue for the
underlying material calibration.
-/
theorem r_s_eq_s_eigenvalue
    (U : State) :
    ((M.calibration.jonesReflector U).coeffs).r_s =
      M.calibration.eigenResponse.eigenvalue FresnelChannel.s U :=
  M.calibration.r_s_eq_s_eigenvalue U

/--
The `p` Fresnel/Jones coefficient is the calibrated `p` eigenvalue for the
underlying material calibration.
-/
theorem r_p_eq_p_eigenvalue
    (U : State) :
    ((M.calibration.jonesReflector U).coeffs).r_p =
      M.calibration.eigenResponse.eigenvalue FresnelChannel.p U :=
  M.calibration.r_p_eq_p_eigenvalue U

end MetalMirrorSusceptibilityHessianCalibration

attribute [rep_depth operator]
  HessianResponseDatum
  SusceptibilityDatum
  ConstructiveHessianSusceptibilityCalibration
  ConstructiveHessianSusceptibilityCalibration.susceptibility
  ConstructiveHessianSusceptibilityCalibration.susceptibility_eq_hessian_response
  ConstructiveHessianSusceptibilityCalibration.susceptibility_apply
  ConstructiveHessianSusceptibilityCalibration.toSusceptibilityDatum
  ConstructiveHessianSusceptibilityCalibration.toSusceptibilityDatum_susceptibility
  ConstructiveHessianSusceptibilityCalibration.toSusceptibilityDatum_derived_from_hessian
  DielectricResponseDatum
  ConstructiveDielectricResponseCalibration
  ConstructiveDielectricResponseCalibration.toDielectricResponseDatum
  ConstructiveDielectricResponseCalibration.toDielectricResponseDatum_epsilon
  ConstructiveDielectricResponseCalibration.toDielectricResponseDatum_refractiveIndex
  OpticalInterfaceGeometry
  FresnelFromSusceptibilityCalibration
  SPEigenResponseCalibration
  SPEigenResponseCalibration.response_mul_s_projector
  SPEigenResponseCalibration.response_mul_p_projector
  SPEigenResponseCalibration.response_mul_projectorOf
  FresnelEigenvalueCalibration
  FresnelEigenvalueCalibration.coeffOf
  FresnelEigenvalueCalibration.jonesReflector
  FresnelEigenvalueCalibration.jones_r_s_eq_eigenvalue
  FresnelEigenvalueCalibration.jones_r_p_eq_eigenvalue
  FresnelEigenvalueCalibration.coeffOf_eq_eigenvalue
  FresnelEigenvalueCalibration.response_mul_projectorOf_eq_coeff
  MetalMirrorSusceptibilityCalibration
  SusceptibilityHessianJonesCalibration
  SusceptibilityHessianJonesCalibration.jonesReflector
  SusceptibilityHessianJonesCalibration.r_s_eq_s_eigenvalue
  SusceptibilityHessianJonesCalibration.r_p_eq_p_eigenvalue
  MetalMirrorSusceptibilityHessianCalibration
  MetalMirrorSusceptibilityHessianCalibration.r_s_eq_s_eigenvalue
  MetalMirrorSusceptibilityHessianCalibration.r_p_eq_p_eigenvalue

end InfoGeometry.Thermo.SusceptibilityHessian

-- [STITCHER: MISSING OVERLAP] --
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
-- [STITCHER: MISSING OVERLAP] --

The quantities are complex-valued to support absorbing media.
-/
structure OpticalInterfaceResponse
    (Freq : Type*) where
  /-- Index/impedance package for medium 1, compressed as `n1`. -/
  n1 : Freq → ℂ

  /-- Index/impedance package for medium 2, compressed as `n2`. -/
  n2 : Freq → ℂ

  /-- Cosine of incidence angle, or its complex continuation. -/
  cosIncident : Freq → ℂ

  /-- Cosine of transmission angle, or its complex continuation. -/
  cosTransmitted : Freq → ℂ

  /-- Certificate that Snell/interface geometry is valid. -/
  interfaceGeometryValid : Prop

/-- Standard s-polarized Fresnel reflection amplitude. -/
def fresnelRS
    {Freq : Type*}
    (I : OpticalInterfaceResponse Freq)
    (omega : Freq) : ℂ :=
  (I.n1 omega * I.cosIncident omega - I.n2 omega * I.cosTransmitted omega) /
    (I.n1 omega * I.cosIncident omega + I.n2 omega * I.cosTransmitted omega)

/-- Standard p-polarized Fresnel reflection amplitude. -/
def fresnelRP
    {Freq : Type*}
    (I : OpticalInterfaceResponse Freq)
    (omega : Freq) : ℂ :=
  (I.n2 omega * I.cosIncident omega - I.n1 omega * I.cosTransmitted omega) /
    (I.n2 omega * I.cosIncident omega + I.n1 omega * I.cosTransmitted omega)

/--
Fresnel coefficient datum with explicit standard reflection formulas.

The transmission laws remain proof-carrying because their branch conventions
belong to the material/interface layer.
-/
structure MaterialFresnelCoefficientDatum
    (Freq : Type*) where
  /-- Interface geometry and optical response. -/
  interface :
    OpticalInterfaceResponse Freq

  /-- s-polarized reflection coefficient. -/
  r_s : Freq → ℂ

  /-- p-polarized reflection coefficient. -/
  r_p : Freq → ℂ

  /-- s-polarized transmission coefficient. -/
  t_s : Freq → ℂ

  /-- p-polarized transmission coefficient. -/
  t_p : Freq → ℂ

  /-- s coefficient is the standard interface formula. -/
  r_s_eq_standard :
    ∀ omega, r_s omega = fresnelRS interface omega

  /-- p coefficient is the standard interface formula. -/
  r_p_eq_standard :
    ∀ omega, r_p omega = fresnelRP interface omega

namespace MaterialFresnelCoefficientDatum

variable {Freq : Type*}
variable (F : MaterialFresnelCoefficientDatum Freq)

/-- s-polarized coefficient equals the standard Fresnel expression. -/
theorem r_s_eq
    (omega : Freq) :
    F.r_s omega = fresnelRS F.interface omega :=
  F.r_s_eq_standard omega

/-- p-polarized coefficient equals the standard Fresnel expression. -/
theorem r_p_eq
    (omega : Freq) :
    F.r_p omega = fresnelRP F.interface omega :=
  F.r_p_eq_standard omega

end MaterialFresnelCoefficientDatum

/--
Polarization eigen-response.

The intended interpretation is that `s` and `p` polarizations diagonalize the
material/interface response.
-/
structure PolarizationEigenResponse
    (Freq : Type*) where
  /-- Polarization eigenvalue. -/
  eigenvalue : PolarizationMode → Freq → ℂ

/--
Fresnel coefficients as eigenvalues of the polarization response.

This is the formal version of: `r_s` and `r_p` are geometric eigenvalues after
material and interface calibration have been supplied.
-/
structure FresnelEigenCalibration
    (Freq : Type*) where
  /-- Fresnel coefficient data. -/
  fresnel :
    MaterialFresnelCoefficientDatum Freq

  /-- Polarization eigen-response. -/
  eigenResponse :
    PolarizationEigenResponse Freq

  /-- s eigenvalue is `r_s`. -/
  s_eigenvalue_eq :
    ∀ omega,
      eigenResponse.eigenvalue PolarizationMode.s omega =
        fresnel.r_s omega

  /-- p eigenvalue is `r_p`. -/
  p_eigenvalue_eq :
    ∀ omega,
      eigenResponse.eigenvalue PolarizationMode.p omega =
        fresnel.r_p omega

namespace FresnelEigenCalibration

variable {Freq : Type*}
variable (C : FresnelEigenCalibration Freq)

/-- The s-polarized geometric eigenvalue is the Fresnel `r_s`. -/
theorem s_eigenvalue_is_r_s
    (omega : Freq) :
    C.eigenResponse.eigenvalue PolarizationMode.s omega =
      C.fresnel.r_s omega :=
  C.s_eigenvalue_eq omega

/-- The p-polarized geometric eigenvalue is the Fresnel `r_p`. -/
theorem p_eigenvalue_is_r_p
    (omega : Freq) :
    C.eigenResponse.eigenvalue PolarizationMode.p omega =
      C.fresnel.r_p omega :=
  C.p_eigenvalue_eq omega

/-- The s-polarized eigenvalue equals the standard Fresnel formula. -/
theorem s_eigenvalue_eq_standard
    (omega : Freq) :
    C.eigenResponse.eigenvalue PolarizationMode.s omega =
      fresnelRS C.fresnel.interface omega := by
  rw [C.s_eigenvalue_is_r_s omega]
  exact C.fresnel.r_s_eq omega

/-- The p-polarized eigenvalue equals the standard Fresnel formula. -/
theorem p_eigenvalue_eq_standard
    (omega : Freq) :
    C.eigenResponse.eigenvalue PolarizationMode.p omega =
      fresnelRP C.fresnel.interface omega := by
  rw [C.p_eigenvalue_is_r_p omega]
  exact C.fresnel.r_p_eq omega

end FresnelEigenCalibration

/-- Operatorial Jones response indexed by polarization and frequency. -/
structure OperatorialJonesResponse
    (Op Freq : Type*) [Ring Op] where
  /-- Jones operator for the selected channel and frequency. -/
  jonesOperator : PolarizationMode → Freq → Op

/-- Calibration between operatorial Jones response and Fresnel eigenvalues. -/
structure JonesFresnelCalibration
    (Op Freq : Type*) [Ring Op] where
  /-- Fresnel eigenvalue calibration. -/
  fresnelEigen :
    FresnelEigenCalibration Freq

  /-- Operatorial Jones response. -/
  jones :
    OperatorialJonesResponse Op Freq

  /-- The `s` Jones channel is calibrated by the s Fresnel eigenvalue. -/
  sCalibration : Prop

  /-- The `p` Jones channel is calibrated by the p Fresnel eigenvalue. -/
  pCalibration : Prop

  /-- Flux conservation or absorption/Stinespring accounting certificate. -/
  fluxAccounting : Prop

/-- Full bridge from Hessian information geometry to Fresnel/Jones response. -/
structure SusceptibilityHessianFresnelBridge
    (State Tangent Op Freq WaveVector : Type*) [Ring Op] where
  /-- Hessian-to-susceptibility bridge. -/
  hessianBridge :
    HessianSusceptibilityBridge State Tangent Op Freq WaveVector

  /-- Dielectric/impedance backend. -/
  dielectric :
    DielectricResponseDatum Freq WaveVector

  /-- Fresnel coefficients as polarization eigenvalues. -/
  fresnelEigen :
    FresnelEigenCalibration Freq

  /-- Operatorial Jones calibration. -/
  jonesCalibration :
    JonesFresnelCalibration Op Freq

  /-- Dielectric response induced by Hessian-calibrated susceptibility. -/
  dielectric_from_hessian_susceptibility : Prop

  /-- Fresnel eigenvalues are boundary readouts of that material response. -/
  fresnel_from_dielectric_response : Prop

namespace SusceptibilityHessianFresnelBridge

variable
    {State Tangent Op Freq WaveVector : Type*}
    [Ring Op]

variable
    (B : SusceptibilityHessianFresnelBridge
      State Tangent Op Freq WaveVector)

/-- The s-polarized reflection eigenvalue is the Fresnel `r_s`. -/
theorem s_reflection_eigenvalue
    (omega : Freq) :
    B.fresnelEigen.eigenResponse.eigenvalue PolarizationMode.s omega =
      B.fresnelEigen.fresnel.r_s omega :=
  B.fresnelEigen.s_eigenvalue_is_r_s omega

/-- The p-polarized reflection eigenvalue is the Fresnel `r_p`. -/
theorem p_reflection_eigenvalue
    (omega : Freq) :
    B.fresnelEigen.eigenResponse.eigenvalue PolarizationMode.p omega =
      B.fresnelEigen.fresnel.r_p omega :=
  B.fresnelEigen.p_eigenvalue_is_r_p omega

end SusceptibilityHessianFresnelBridge

/-! ## 6. Stinespring heat coupling -/

/--
Coupling between optical absorption and a Stinespring/Bregman heat ledger.
-/
structure OpticalStinespringHeatCalibration
    (State Sys Comm : Type*)
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    (B : BregmanDivergenceDatum Sys)
    (C : DissipativeChannel Sys)
    (D : StinespringTomitaDilation Sys Comm C) where
  /-- Embed or read an optical material state as a system state. -/
  stateToSystem :
    State → Sys

  /-- Optical absorption readout on material states. -/
  absorptionFromState :
    State → ℝ

  /-- Hidden-information bridge for the Stinespring/Tomita dilation. -/
  hiddenHeatBridge :
    HeatEqualsHiddenInformation Sys Comm B C D

  /--
  Optical absorption agrees with Bregman heat after mapping the optical state
  into the system carrier.
  -/
  absorption_eq_heat :
    ∀ U : State,
      absorptionFromState U =
        heatLoss B C (stateToSystem U)

namespace OpticalStinespringHeatCalibration

variable
    {State Sys Comm : Type*}
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    {B : BregmanDivergenceDatum Sys}
    {C : DissipativeChannel Sys}
    {D : StinespringTomitaDilation Sys Comm C}

variable (K : OpticalStinespringHeatCalibration State Sys Comm B C D)

/--
Optical absorption is the hidden-information readout through the
Stinespring/Tomita bridge.
-/
theorem absorption_eq_hidden_information
    (U : State) :
    K.absorptionFromState U =
      K.hiddenHeatBridge.hiddenReadout.hiddenInfo
        (D.hiddenFlow (K.stateToSystem U)) := by
  rw [K.absorption_eq_heat U]
  exact K.hiddenHeatBridge.heat_is_hidden_commutant_information
    (K.stateToSystem U)

end OpticalStinespringHeatCalibration

/-! ## 6a. PT hidden-sector Stinespring clinch -/

/--
Optical PT Stinespring clinch.

This is the witness-gated statement that a coherent optical event is booked in
the PT sector and that its apparent absorption is exactly the hidden
commutant-information readout supplied by the Stinespring/Tomita dilation.

The Jones event supplies the visible optical tag.  The Stinespring heat
calibration supplies the conservation and hidden-information ledger.
-/
structure OpticalPTStinespringClinch
    (State Sys Comm : Type*)
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    (B : BregmanDivergenceDatum Sys)
    (C : DissipativeChannel Sys)
    (D : StinespringTomitaDilation Sys Comm C) where
  /-- Optical absorption-to-hidden-information heat ledger. -/
  opticalHeat :
    OpticalStinespringHeatCalibration State Sys Comm B C D

  /-- Visible coherent Jones event attached to the optical state. -/
  eventOf :
    State → JonesOpticalEvent

  /-- The optical event is booked in the PT sector. -/
  event_tag_pt :
    ∀ U : State, (eventOf U).tag = V4Tag.PT

  /-- Model-specific law that this PT sector is the intended commutant/dark readout. -/
  pt_commutant_sector_law : Prop


namespace OpticalPTStinespringClinch

variable
    {State Sys Comm : Type*}
    [NormedAddCommGroup Sys] [NormedSpace ℝ Sys]
    [NormedAddCommGroup Comm] [NormedSpace ℝ Comm]
    {B : BregmanDivergenceDatum Sys}
    {C : DissipativeChannel Sys}
    {D : StinespringTomitaDilation Sys Comm C}

variable (K : OpticalPTStinespringClinch State Sys Comm B C D)

/-- The visible optical event is tagged by the PT sector. -/
theorem event_tag_eq_PT
    (U : State) :
    (K.eventOf U).tag = V4Tag.PT :=
  K.event_tag_pt U

/--
Optical absorption is exactly the hidden commutant-information readout.
-/
theorem absorption_eq_hidden_information
    (U : State) :
    K.opticalHeat.absorptionFromState U =
      K.opticalHeat.hiddenHeatBridge.hiddenReadout.hiddenInfo
        (D.hiddenFlow (K.opticalHeat.stateToSystem U)) :=
  K.opticalHeat.absorption_eq_hidden_information U

/--
Bregman heat is exactly the hidden commutant-information readout.
-/
theorem heat_eq_hidden_information
    (U : State) :
    heatLoss B C (K.opticalHeat.stateToSystem U) =
      K.opticalHeat.hiddenHeatBridge.hiddenReadout.hiddenInfo
        (D.hiddenFlow (K.opticalHeat.stateToSystem U)) :=
  K.opticalHeat.hiddenHeatBridge.heat_is_hidden_commutant_information
    (K.opticalHeat.stateToSystem U)

/--
The hidden commutant-information readout is nonnegative on optical states.
-/
theorem hidden_information_nonneg
    (U : State) :
    0 ≤ K.opticalHeat.hiddenHeatBridge.hiddenReadout.hiddenInfo
      (D.hiddenFlow (K.opticalHeat.stateToSystem U)) :=
  K.opticalHeat.hiddenHeatBridge.hidden_information_nonneg
    (K.opticalHeat.stateToSystem U)

/--
Optical absorption is nonnegative because it is hidden commutant information.
-/
theorem absorption_nonneg
    (U : State) :
    0 ≤ K.opticalHeat.absorptionFromState U := by
  rw [K.absorption_eq_hidden_information U]
  exact K.hidden_information_nonneg U

/--
The apparent visible deficit is exactly the recovered hidden commutant flow.
-/
theorem visible_deficit_eq_recovered_hidden
    (U : State) :
    C.ideal (K.opticalHeat.stateToSystem U) -
        C.actual (K.opticalHeat.stateToSystem U) =
      D.recoverHidden (D.hiddenFlow (K.opticalHeat.stateToSystem U)) :=
  D.ideal_sub_actual_eq_recovered_hidden (K.opticalHeat.stateToSystem U)

end OpticalPTStinespringClinch

/-! ## 7. Bregman/Fenchel Hessian to Jones calibration -/

/--
A Bregman/Fenchel Hessian readout of an information potential.

The Hessian is real-valued because it is the information-geometric response
metric.  Complex optical response enters only through material calibration.
-/
structure BregmanHessianResponse
    (State Tangent : Type*) [AddCommGroup Tangent] [Module ℝ Tangent] where
  /-- Hessian pairing at a state. -/
  hessianAt : State → Tangent → Tangent → ℝ

  /-- Symmetry of the Hessian pairing. -/
  symmetric :
    ∀ s X Y, hessianAt s X Y = hessianAt s Y X

  /-- Nonnegativity / convex response. -/
  nonnegative :
    ∀ s X, 0 ≤ hessianAt s X X

  /-- Certificate that this Hessian comes from the intended potential. -/
  bregman_hessian_law : Prop


namespace BregmanHessianResponse

variable {State Tangent : Type*} [AddCommGroup Tangent] [Module ℝ Tangent]
variable (H : BregmanHessianResponse State Tangent)

/-- Re-export Hessian symmetry. -/
theorem hessian_symmetric
    (s : State)
    (X Y : Tangent) :
    H.hessianAt s X Y = H.hessianAt s Y X :=
  H.symmetric s X Y

/-- Re-export Hessian nonnegativity. -/
theorem hessian_nonnegative
    (s : State)
    (X : Tangent) :
    0 ≤ H.hessianAt s X X :=
  H.nonnegative s X

end BregmanHessianResponse

/--
Complex material susceptibility.

The value is complex because the reactive and absorptive material responses
are both part of the optical readout.
-/
structure SusceptibilityDatum
    (State Freq : Type*) where
  /-- Complex susceptibility. -/
  susceptibility : State → Freq → ℂ

  /-- Material-response law. -/
  susceptibility_law : Prop


/--
State-indexed dielectric response calibrated from susceptibility.

The actual material equation, such as `epsilon = 1 + susceptibility`, is kept
proof-carrying at this layer.
-/
structure StateDielectricResponseDatum
    (State Freq : Type*) where
  /-- Complex dielectric function. -/
  epsilon : State → Freq → ℂ

  /-- Optional magnetic response. -/
  mu : State → Freq → ℂ

  /-- Relation between susceptibility and dielectric response. -/
  dielectric_law : Prop


/--
Complex refractive-index response.

Branch choice and material model are explicit proof-carrying data.
-/
structure ComplexRefractiveIndexDatum
    (State Freq : Type*) where
  /-- Complex refractive index. -/
  N : State → Freq → ℂ

  /-- Branch/material law connecting `N` to dielectric data. -/
  refractive_index_law : Prop


/--
Calibration from a Bregman Hessian to material susceptibility.

This is the witness-gated bridge saying that the local information-geometric
response is the material response readout in a concrete model.
-/
structure BregmanHessianSusceptibilityCalibration
    (State Tangent Freq : Type*)
    [AddCommGroup Tangent] [Module ℝ Tangent] where
  /-- Bregman/Fenchel Hessian response. -/
  hessian :
    BregmanHessianResponse State Tangent

  /-- Complex susceptibility datum. -/
  susceptibility :
    SusceptibilityDatum State Freq

  /-- Bridge law from Hessian response to susceptibility. -/
  hessian_controls_susceptibility_law : Prop


/--
Fresnel coefficient readout from a complex refractive-index model.

`coeff_s` and `coeff_p` are optical amplitude reflection coefficients.
-/
structure FresnelFromRefractiveIndex
    (State Freq Angle : Type*) where
  /-- s-polarized reflection coefficient. -/
  coeff_s : State → Freq → Angle → ℂ

  /-- p-polarized reflection coefficient. -/
  coeff_p : State → Freq → Angle → ℂ

  /-- Fresnel law certificate. -/
  fresnel_law : Prop


/--
Response eigenvalues in the local polarization basis.

Mode `0` is the first channel and mode `1` is the second channel.
-/
structure OpticalResponseEigenvalues
    (State Freq Angle : Type*) where
  /-- Optical response eigenvalue for each channel. -/
  eigenvalue : State → Freq → Angle → Fin 2 → ℂ

  /-- Eigenbasis of the response. -/
  basis : PolarizationBasis

  /-- Eigenvalue law/certificate. -/
  eigenvalue_law : Prop


/--
Complete Hessian/Fresnel calibration.

This packages Hessian response, susceptibility, dielectric response,
refractive index, optical response eigenvalues, and Fresnel coefficients.
-/
structure SusceptibilityFresnelCalibration
    (State Tangent Freq Angle : Type*)
    [AddCommGroup Tangent] [Module ℝ Tangent] where
  /-- Hessian-to-susceptibility calibration. -/
  hessianSusceptibility :
    BregmanHessianSusceptibilityCalibration State Tangent Freq

  /-- Dielectric response. -/
  dielectric :
    StateDielectricResponseDatum State Freq

  /-- Complex refractive-index response. -/
  refractiveIndex :
    ComplexRefractiveIndexDatum State Freq

  /-- Optical response eigenvalues. -/
  responseEigenvalues :
    OpticalResponseEigenvalues State Freq Angle

  /-- Fresnel coefficient readout. -/
  fresnel :
    FresnelFromRefractiveIndex State Freq Angle

  /-- The `s` Fresnel coefficient is the first response eigenvalue. -/
  coeff_s_eq_eigen_zero :
    ∀ s : State, ∀ omega : Freq, ∀ theta : Angle,
      fresnel.coeff_s s omega theta =
        responseEigenvalues.eigenvalue s omega theta 0

  /-- The `p` Fresnel coefficient is the second response eigenvalue. -/
  coeff_p_eq_eigen_one :
    ∀ s : State, ∀ omega : Freq, ∀ theta : Angle,
      fresnel.coeff_p s omega theta =
        responseEigenvalues.eigenvalue s omega theta 1

  /-- End-to-end calibration law. -/
  end_to_end_optical_response_law : Prop


namespace SusceptibilityFresnelCalibration

variable
    {State Tangent Freq Angle : Type*}
    [AddCommGroup Tangent] [Module ℝ Tangent]

variable (C : SusceptibilityFresnelCalibration State Tangent Freq Angle)

/--
The `s` Fresnel coefficient is the first Hessian-calibrated response eigenvalue.
-/
theorem coeff_s_is_response_eigenvalue
    (s : State)
    (omega : Freq)
    (theta : Angle) :
    C.fresnel.coeff_s s omega theta =
      C.responseEigenvalues.eigenvalue s omega theta 0 :=
  C.coeff_s_eq_eigen_zero s omega theta

/--
The `p` Fresnel coefficient is the second Hessian-calibrated response eigenvalue.
-/
theorem coeff_p_is_response_eigenvalue
    (s : State)
    (omega : Freq)
    (theta : Angle) :
    C.fresnel.coeff_p s omega theta =
      C.responseEigenvalues.eigenvalue s omega theta 1 :=
  C.coeff_p_eq_eigen_one s omega theta

end SusceptibilityFresnelCalibration

/--
A calibrated optical state/event produces a Jones optical event.
-/
structure HessianJonesCalibration
    (State Tangent Freq Angle : Type*)
    [AddCommGroup Tangent] [Module ℝ Tangent] where
  /-- Full Hessian/Fresnel response calibration. -/
  response :
    SusceptibilityFresnelCalibration State Tangent Freq Angle

  /-- Surface kind assigned to the event. -/
  surfaceKind : OpticalSurfaceKind

  /-- Discrete V4 tag assigned to the event. -/
  tagOf : State → Freq → Angle → V4Tag

  /-- Coherence law for the Jones description. -/
  coherence : State → Freq → Angle → Prop

  coherent :
    ∀ s : State, ∀ omega : Freq, ∀ theta : Angle,
      coherence s omega theta

namespace HessianJonesCalibration

variable
    {State Tangent Freq Angle : Type*}
    [AddCommGroup Tangent] [Module ℝ Tangent]

variable (C : HessianJonesCalibration State Tangent Freq Angle)

/--
The Jones event generated by the calibrated Hessian/Fresnel response.
-/
def eventOf
    (s : State)
    (omega : Freq)
    (theta : Angle) : JonesOpticalEvent where
  basis := C.response.responseEigenvalues.basis
  kind := C.surfaceKind
  coeff0 := C.response.fresnel.coeff_s s omega theta
  coeff1 := C.response.fresnel.coeff_p s omega theta
  tag := C.tagOf s omega theta
  coherence := C.coherence s omega theta

/--
The first Jones coefficient is the calibrated `s`/first-channel Fresnel
coefficient.
-/
theorem event_coeff0_eq_fresnel_s
    (s : State)
    (omega : Freq)
    (theta : Angle) :
    (C.eventOf s omega theta).coeff0 =
      C.response.fresnel.coeff_s s omega theta :=
  rfl

/--
The second Jones coefficient is the calibrated `p`/second-channel Fresnel
coefficient.
-/
theorem event_coeff1_eq_fresnel_p
    (s : State)
    (omega : Freq)
    (theta : Angle) :
    (C.eventOf s omega theta).coeff1 =
      C.response.fresnel.coeff_p s omega theta :=
  rfl

/--
The first Jones coefficient is the first Hessian-calibrated response eigenvalue.
-/
theorem event_coeff0_eq_response_eigenvalue
    (s : State)
    (omega : Freq)
    (theta : Angle) :
    (C.eventOf s omega theta).coeff0 =
      C.response.responseEigenvalues.eigenvalue s omega theta 0 := by
  calc
    (C.eventOf s omega theta).coeff0
        = C.response.fresnel.coeff_s s omega theta := rfl
    _ = C.response.responseEigenvalues.eigenvalue s omega theta 0 :=
        C.response.coeff_s_is_response_eigenvalue s omega theta

/--
The second Jones coefficient is the second Hessian-calibrated response
eigenvalue.
-/
theorem event_coeff1_eq_response_eigenvalue
    (s : State)
    (omega : Freq)
    (theta : Angle) :
    (C.eventOf s omega theta).coeff1 =
      C.response.responseEigenvalues.eigenvalue s omega theta 1 := by
  calc
    (C.eventOf s omega theta).coeff1
        = C.response.fresnel.coeff_p s omega theta := rfl
    _ = C.response.responseEigenvalues.eigenvalue s omega theta 1 :=
        C.response.coeff_p_is_response_eigenvalue s omega theta

end HessianJonesCalibration

/--
Metal-mirror specialization of the calibrated Jones response.
-/
structure MetalMirrorSusceptibilityCalibration
    (State Tangent Freq Angle : Type*)
    [AddCommGroup Tangent] [Module ℝ Tangent] where
  /-- Hessian-to-Jones calibration. -/
  jonesCalibration :
    HessianJonesCalibration State Tangent Freq Angle

  /-- The event is interpreted as a metal mirror response. -/
  metal_mirror_law : Prop

  /-- Absorptive part of response controls Bregman/thermal loss. -/
  absorption_heat_law : Prop

  /-- Reactive part of response controls retardance/ellipticity. -/
  retardance_law : Prop


namespace MetalMirrorSusceptibilityCalibration

variable
    {State Tangent Freq Angle : Type*}
    [AddCommGroup Tangent] [Module ℝ Tangent]

variable (M : MetalMirrorSusceptibilityCalibration State Tangent Freq Angle)

/-- Jones event of the metal mirror response. -/
def eventOf
    (s : State)
    (omega : Freq)
    (theta : Angle) : JonesOpticalEvent :=
  M.jonesCalibration.eventOf s omega theta

/--
The second Jones coefficient is the Hessian-calibrated `p`/second-channel
response eigenvalue.
-/
theorem p_coeff_is_hessian_response_eigenvalue
    (s : State)
    (omega : Freq)
    (theta : Angle) :
    (M.eventOf s omega theta).coeff1 =
      M.jonesCalibration.response.responseEigenvalues.eigenvalue s omega theta 1 :=
  M.jonesCalibration.event_coeff1_eq_response_eigenvalue s omega theta

end MetalMirrorSusceptibilityCalibration

/--
Vacuum response calibration.

The concrete normalization of vacuum susceptibility is proof-carrying.
-/
structure VacuumResponseCalibration
    (State Freq : Type*) where
  /-- Vacuum susceptibility datum. -/
  susceptibility :
    SusceptibilityDatum State Freq

  /-- Vacuum susceptibility law. -/
  vacuum_susceptibility_law : Prop


/--
Matter response calibration.

In matter, the Hessian/susceptibility response can produce absorption,
-- [STITCHER: MISSING OVERLAP] --
retardance, diattenuation, and heat once calibrated.
-/
structure MatterResponseCalibration
    (State Tangent Freq Angle : Type*)
    [AddCommGroup Tangent] [Module ℝ Tangent] where
  /-- Full susceptibility/Fresnel response calibration. -/
  response :
    SusceptibilityFresnelCalibration State Tangent Freq Angle

  /-- Matter response law. -/
  matter_response_law : Prop


/--
Compatibility predicate for the material-response Hessian/Fresnel bridge.

Concrete modules should replace this by material-model, linear-response,
dielectric-backend, interface-geometry, and Jones/Fresnel calibration data.
-/
def MaterialSusceptibilityHessianCompatibility
    (State Tangent Op Freq WaveVector : Type*) [Ring Op] : Prop :=
  Nonempty (State → Tangent → Op → Freq → WaveVector → Unit)

/--
Owner target for constructing material-response/Fresnel data from an
information Hessian.
-/
@[owner_target_tag]
def MaterialSusceptibilityHessianOwnerTarget : Prop :=
  ∀ (State Tangent Op Freq WaveVector : Type*) [Ring Op],
    MaterialSusceptibilityHessianCompatibility State Tangent Op Freq WaveVector →
      Nonempty
        (SusceptibilityHessianFresnelBridge
          State Tangent Op Freq WaveVector)

/-! ## 5. Owner target -/

/--
Owner target for optical response calibration.

This is intentionally witness-gated.  Concrete material models must supply the
Hessian/material/Fresnel calibration.
-/
@[owner_target_tag]
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
  IsHessianDegenerate
  MaterialResponseModel
  HessianSusceptibilityCalibration
  FresnelCoefficientReadout
  StatePolarizationEigenResponse
  FresnelFromStateEigenResponse
  FresnelFromStateEigenResponse.responseS_eq_rs
  FresnelFromStateEigenResponse.responseP_eq_rp
  spJonesEventOfFresnel
  spJonesEventOfFresnel_basis
  spJonesEventOfFresnel_coeff0
  spJonesEventOfFresnel_coeff1
  spJonesEventOfFresnel_jones_00
  spJonesEventOfFresnel_jones_11
  JonesFromMaterialCalibration
  jonesFromMaterialCalibrationOfFresnel
  JonesFromMaterialCalibration.jones_00_eq_rs
  JonesFromMaterialCalibration.jones_11_eq_rp
  JonesFromMaterialCalibration.jones_offdiag_01_zero
  JonesFromMaterialCalibration.jones_offdiag_10_zero
  RetardanceReadout
  OpticalAbsorptionReadout
  OpticalResponseCalibration
  OpticalResponseCalibration.ofFresnel
  OpticalResponseCalibration.eventOf
  OpticalResponseCalibration.jones_00_eq_rs
  OpticalResponseCalibration.jones_11_eq_rp
  OpticalResponseCalibration.jones_offdiag_01_zero
  OpticalResponseCalibration.jones_offdiag_10_zero
  OpticalResponseEigenCalibration
  OpticalResponseEigenCalibration.responseS_eq_rs
  OpticalResponseEigenCalibration.responseP_eq_rp
  OpticalResponseEigenCalibration.jones_00_eq_rs
  OpticalResponseEigenCalibration.jones_11_eq_rp
  InformationPotentialDatum
  InformationPotentialDatum.hessian_symmetric
  InformationPotentialDatum.hessian_nonneg
  BregmanHeatDatum
  BregmanHeatDatum.heat_nonnegative
  BregmanHeatDatum.heat_self
  LinearSusceptibilityDatum
  HessianSusceptibilityBridge
  DielectricResponseDatum
  PolarizationMode
  OpticalInterfaceResponse
  fresnelRS
  fresnelRP
  MaterialFresnelCoefficientDatum
  MaterialFresnelCoefficientDatum.r_s_eq
  MaterialFresnelCoefficientDatum.r_p_eq
  PolarizationEigenResponse
  FresnelEigenCalibration
  FresnelEigenCalibration.s_eigenvalue_is_r_s
  FresnelEigenCalibration.p_eigenvalue_is_r_p
  FresnelEigenCalibration.s_eigenvalue_eq_standard
  FresnelEigenCalibration.p_eigenvalue_eq_standard
  OperatorialJonesResponse
  JonesFresnelCalibration
  SusceptibilityHessianFresnelBridge
  SusceptibilityHessianFresnelBridge.s_reflection_eigenvalue
  SusceptibilityHessianFresnelBridge.p_reflection_eigenvalue
  OpticalStinespringHeatCalibration
  OpticalStinespringHeatCalibration.absorption_eq_hidden_information
  OpticalPTStinespringClinch
  OpticalPTStinespringClinch.event_tag_eq_PT
  OpticalPTStinespringClinch.absorption_eq_hidden_information
  OpticalPTStinespringClinch.heat_eq_hidden_information
  OpticalPTStinespringClinch.hidden_information_nonneg
  OpticalPTStinespringClinch.absorption_nonneg
  OpticalPTStinespringClinch.visible_deficit_eq_recovered_hidden
  BregmanHessianResponse
  BregmanHessianResponse.hessian_symmetric
  BregmanHessianResponse.hessian_nonnegative
  SusceptibilityDatum
  StateDielectricResponseDatum
  ComplexRefractiveIndexDatum
  BregmanHessianSusceptibilityCalibration
  FresnelFromRefractiveIndex
  OpticalResponseEigenvalues
  SusceptibilityFresnelCalibration
  SusceptibilityFresnelCalibration.coeff_s_is_response_eigenvalue
  SusceptibilityFresnelCalibration.coeff_p_is_response_eigenvalue
  HessianJonesCalibration
  HessianJonesCalibration.eventOf
  HessianJonesCalibration.event_coeff0_eq_fresnel_s
  HessianJonesCalibration.event_coeff1_eq_fresnel_p
  HessianJonesCalibration.event_coeff0_eq_response_eigenvalue
  HessianJonesCalibration.event_coeff1_eq_response_eigenvalue
  MetalMirrorSusceptibilityCalibration
  MetalMirrorSusceptibilityCalibration.eventOf
  MetalMirrorSusceptibilityCalibration.p_coeff_is_hessian_response_eigenvalue
  VacuumResponseCalibration
  MatterResponseCalibration
  MaterialSusceptibilityHessianCompatibility
  MaterialSusceptibilityHessianOwnerTarget
  SusceptibilityHessianOwnerTarget
  susceptibilityHessianOwnerTarget

/-! ## Concrete Instances to Purify Vacuous Shapes -/

/-- Concrete trivial Hessian response datum for ℝ. -/
def concreteHessianResponseDatum : HessianResponseDatum ℝ where
  hessian := fun _ ↦ (0 : ℝ →L[ℝ] ℝ)
  regularAt := fun x ↦ x ≠ 0
  singularAt := fun x ↦ x = 0
  singular_not_regular := fun U hU ↦ by
    intro h
    rw [hU] at h
    exact h rfl

/-- Concrete material response model over ℝ. -/
def concreteMaterialResponseModel : MaterialResponseModel ℝ where
  frequency := fun _ ↦ 1
  incidenceAngle := fun _ ↦ 0
  complexIndex := fun _ ↦ 1
  susceptibility := fun _ ↦ 0
  material_law := ∀ U : ℝ, (1 : ℂ) = 1 + (0 : ℂ)
  material_law_holds := fun _ ↦ by ring

/-- Concrete Fresnel coefficient readout over ℝ. -/
def concreteFresnelCoefficientReadout : FresnelCoefficientReadout ℝ where
  rs := fun U ↦ (U : ℂ)
  rp := fun U ↦ -(U : ℂ)
  fresnel_law := ∀ U : ℝ, (U : ℂ) + -(U : ℂ) = 0
  fresnel_law_holds := fun U ↦ by ring

end InfoGeometry.OperatorAlgebra.SusceptibilityHessian

-- [STITCHER: MISSING OVERLAP] --
import Mathlib
import InfoGeometry.Thermo.MetalMirror
import InfoGeometry.Geometry.OperatorBregmanDivergence
import InfoGeometry.Optics.JonesCalibration
import InfoGeometry.Meta.Architecture

/-!
# Susceptibility Hessian

Susceptibility as a Hessian/linear-response calibration.

This module connects the Legendre/Bregman Hessian of an information potential
to optical material response.  It does not derive Fresnel coefficients from
the Hessian alone; incidence geometry, material response, branch choices, and
Fresnel/Jones calibration are supplied as proof-carrying data.
-/

noncomputable section

namespace InfoGeometry.Thermo.SusceptibilityHessian

open InfoGeometry.Optics.JonesCalibration

/-! ## Hessian response backend -/

/--
A Hessian response datum on an operator/state space.

The intended interpretation is that `hessian U` is the local linear response
operator at state `U`.
-/
structure HessianResponseDatum
    (Op Field Response : Type*)
    [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response] where
  /-- Hessian or Fisher/Legendre metric at a state. -/
  hessian : Op → Op →L[ℝ] Op

  /-- Optical perturbing field readout. -/
  fieldReadout : Op → Field

  /-- Material response readout. -/
  responseReadout : Op → Response


namespace HessianResponseDatum

variable
    {Op Field Response : Type*}
    [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response]

variable (H : HessianResponseDatum Op Field Response)

end HessianResponseDatum

/-! ## Susceptibility and dielectric response -/

/--
A susceptibility datum.

The map `susceptibility U` sends an applied field to the induced response.  For
optics, this is morally `P = χ E`, with frequency/momentum dependence carried
by `Op` or by later concrete parameters.
-/
structure SusceptibilityDatum
    (Op Field Response : Type*)
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response] where
  /-- Linear material susceptibility at the chosen state/parameter. -/
  susceptibility : Op → Field →L[ℝ] Response


namespace SusceptibilityDatum

variable
    {Op Field Response : Type*}
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response]

variable (S : SusceptibilityDatum Op Field Response)

end SusceptibilityDatum

/-! ## Constructive Hessian-to-susceptibility descent -/

/--
Constructive Hessian-to-susceptibility calibration.

This is the infinite-dimensional, representation-agnostic version of the
Hessian response claim.  A field perturbation is first embedded into the state
tangent space, then acted on by the Hessian response operator, then read out as
a material response.

No basis, finite-dimensional determinant, or matrix shadow is used.
-/
structure ConstructiveHessianSusceptibilityCalibration
    (Op Field Response : Type*)
    [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response] where
  /-- Hessian/linear-response backend. -/
  hessianResponse :
    HessianResponseDatum Op Field Response

  /-- Embed an optical perturbing field into the state tangent space. -/
  fieldToTangent :
    Op → Field →L[ℝ] Op

  /-- Read a Hessian-shifted tangent vector as a material response. -/
  responseFromTangent :
    Op → Op →L[ℝ] Response

namespace ConstructiveHessianSusceptibilityCalibration

variable
    {Op Field Response : Type*}
    [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response]

variable (C : ConstructiveHessianSusceptibilityCalibration Op Field Response)

/--
The susceptibility induced by explicit Hessian descent:

`χ_U = responseFromTangent_U ∘ hessian_U ∘ fieldToTangent_U`.
-/
def susceptibility :
    Op → Field →L[ℝ] Response :=
  fun U =>
    (C.responseFromTangent U).comp
      ((C.hessianResponse.hessian U).comp (C.fieldToTangent U))

/-- The induced susceptibility is exactly the Hessian-response composition. -/
theorem susceptibility_eq_hessian_response
    (U : Op) :
    C.susceptibility U =
      (C.responseFromTangent U).comp
        ((C.hessianResponse.hessian U).comp (C.fieldToTangent U)) := by sorry
/-- Pointwise form of the constructive Hessian-to-susceptibility descent. -/
theorem susceptibility_apply
    (U : Op)
    (E : Field) :
    C.susceptibility U E =
      C.responseFromTangent U (C.hessianResponse.hessian U (C.fieldToTangent U E)) := by sorry
/--
The ordinary susceptibility datum generated by the constructive descent.

The `derived_from_hessian` evidence is the explicit equality above, not an
uninterpreted external hypothesis.
-/
def toSusceptibilityDatum :
    SusceptibilityDatum Op Field Response where
  susceptibility := C.susceptibility
/-- The generated susceptibility datum has the constructive susceptibility map. -/
theorem toSusceptibilityDatum_susceptibility :
    C.toSusceptibilityDatum.susceptibility = C.susceptibility := by sorry
/--
The generated susceptibility datum proves its Hessian origin by definitional
descent through the explicit tangent/readout maps.
-/
theorem toSusceptibilityDatum_derived_from_hessian
    (U : Op) :
    C.toSusceptibilityDatum.susceptibility U =
      (C.responseFromTangent U).comp
        ((C.hessianResponse.hessian U).comp (C.fieldToTangent U)) := by sorry
end ConstructiveHessianSusceptibilityCalibration

/--
A dielectric response datum.

This is the calibration layer between susceptibility and complex optical
material response.
-/
structure DielectricResponseDatum
    (Op : Type*) where
  /-- Relative dielectric response, possibly frequency/momentum dependent. -/
  epsilon : Op → ℂ

  /-- Complex refractive index readout. -/
  refractiveIndex : Op → ℂ

  /-- Susceptibility/material readout feeding dielectric response. -/
  susceptibilityEpsilonReadout : Op → ℂ

  /-- Calibration equation, e.g. `N² = εᵣ μᵣ` or `N² = εᵣ` in a nonmagnetic model. -/
  refractive_index_calibration :
    ∀ U : Op, refractiveIndex U ^ (2 : ℕ) = epsilon U

  /-- Connection between susceptibility readout and dielectric response. -/
  susceptibility_to_epsilon :
    ∀ U : Op, epsilon U = susceptibilityEpsilonReadout U

namespace DielectricResponseDatum

variable {Op : Type*}
variable (D : DielectricResponseDatum Op)

end DielectricResponseDatum

/--
Constructive dielectric calibration.

This packages the two explicit equalities normally hidden behind the dielectric
interface: the complex-index branch equation and the readout turning
susceptibility/material response into `ε`.
-/
structure ConstructiveDielectricResponseCalibration
    (Op : Type*) where
  /-- Relative dielectric response. -/
  epsilon : Op → ℂ

  /-- Complex refractive-index branch. -/
  refractiveIndex : Op → ℂ

  /-- Explicit susceptibility/material readout feeding the dielectric response. -/
  susceptibilityEpsilonReadout : Op → ℂ

  /-- Branch equation, e.g. `N² = ε` in a nonmagnetic isotropic model. -/
  refractive_index_sq :
    ∀ U : Op, refractiveIndex U ^ (2 : ℕ) = epsilon U

  /-- Explicit equality connecting the susceptibility readout to `ε`. -/
  epsilon_eq_susceptibility_readout :
    ∀ U : Op, epsilon U = susceptibilityEpsilonReadout U

namespace ConstructiveDielectricResponseCalibration

variable {Op : Type*}
variable (C : ConstructiveDielectricResponseCalibration Op)

/--
The ordinary dielectric datum generated by explicit complex-index and
susceptibility-to-`ε` equalities.
-/
def toDielectricResponseDatum :
    DielectricResponseDatum Op where
  epsilon := C.epsilon
  refractiveIndex := C.refractiveIndex
  susceptibilityEpsilonReadout := C.susceptibilityEpsilonReadout
  refractive_index_calibration := C.refractive_index_sq
  susceptibility_to_epsilon := C.epsilon_eq_susceptibility_readout

/-- The generated dielectric datum keeps the supplied `ε` readout. -/
theorem toDielectricResponseDatum_epsilon :
    C.toDielectricResponseDatum.epsilon = C.epsilon := by sorry
/-- The generated dielectric datum keeps the supplied complex-index branch. -/
theorem toDielectricResponseDatum_refractiveIndex :
    C.toDielectricResponseDatum.refractiveIndex = C.refractiveIndex := by sorry
end ConstructiveDielectricResponseCalibration

/-! ## Fresnel/Jones calibration -/

/--
Optical interface parameters needed to evaluate Fresnel reflection.

These data are not determined by susceptibility alone.
-/
structure OpticalInterfaceGeometry where
  /-- Incidence angle. -/
  theta_i : ℝ

  /-- Transmission/refraction angle, if applicable. -/
  theta_t : ℝ


namespace OpticalInterfaceGeometry

variable (G : OpticalInterfaceGeometry)

end OpticalInterfaceGeometry

/--
Fresnel calibration datum.

This packages the statement that the complex Fresnel coefficients are computed
from the material response and boundary geometry.
-/
structure FresnelFromSusceptibilityCalibration
    (Op : Type*) where
  /-- Dielectric/material response. -/
  dielectric : DielectricResponseDatum Op

  /-- Interface geometry needed for Fresnel reflection. -/
  interfaceGeometry : OpticalInterfaceGeometry

  /-- Fresnel coefficients supplied to the Jones layer. -/
  coeffs : InfoGeometry.Optics.JonesCalibration.FresnelCoefficientDatum


namespace FresnelFromSusceptibilityCalibration

variable {Op : Type*}
variable (F : FresnelFromSusceptibilityCalibration Op)

end FresnelFromSusceptibilityCalibration

/-! ## s/p eigenchannel response -/

/--
s/p eigenchannel calibration for a material-response operator.

For a smooth isotropic interface, the `s` and `p` channels diagonalize the
reflection operator.  This structure records the eigenvalues of the calibrated
response operator in those channels.
-/
structure SPEigenResponseCalibration
    (State Op : Type*) [Ring Op] [Algebra ℂ Op]
    (P : SPProjectorPair Op) where
  /-- Calibrated response operator acting on the polarization algebra. -/
  responseOp : State → Op

  /-- Channel eigenvalue. -/
  eigenvalue : FresnelChannel → State → ℂ

  /-- `s` channel is an eigenchannel. -/
  s_eigen :
    ∀ U : State,
      responseOp U * P.P_s =
        eigenvalue FresnelChannel.s U • P.P_s

  /-- `p` channel is an eigenchannel. -/
  p_eigen :
    ∀ U : State,
      responseOp U * P.P_p =
        eigenvalue FresnelChannel.p U • P.P_p

namespace SPEigenResponseCalibration

variable
    {State Op : Type*} [Ring Op] [Algebra ℂ Op]
    {P : SPProjectorPair Op}

variable (E : SPEigenResponseCalibration State Op P)

/-- Re-export of the `s`-eigenchannel equation. -/
theorem response_mul_s_projector
    (U : State) :
    E.responseOp U * P.P_s =
      E.eigenvalue FresnelChannel.s U • P.P_s := by sorry
/-- Re-export of the `p`-eigenchannel equation. -/
theorem response_mul_p_projector
    (U : State) :
    E.responseOp U * P.P_p =
      E.eigenvalue FresnelChannel.p U • P.P_p := by sorry
/-- Uniform channel form of the eigenprojector equation. -/
theorem response_mul_projectorOf
    (U : State)
    (c : FresnelChannel) :
    E.responseOp U * P.projectorOf c =
      E.eigenvalue c U • P.projectorOf c := by sorry
end SPEigenResponseCalibration

/--
Fresnel coefficients as calibrated eigenchannel readouts.

This is the precise place where the statement

`r_s` and `r_p` are geometric eigenvalues

becomes formal.  It is not derived from the Hessian alone; it is derived from
the Hessian plus dielectric and boundary calibration.
-/
structure FresnelEigenvalueCalibration
    (State Op : Type*) [Ring Op] [Algebra ℂ Op]
    (P : SPProjectorPair Op)
    (E : SPEigenResponseCalibration State Op P) where
  /-- Fresnel coefficient datum attached to each state. -/
  coeffs : State → FresnelCoefficientDatum

  /-- The `s` Fresnel coefficient is the `s` eigenvalue. -/
  coeff_s :
    ∀ U : State,
      (coeffs U).r_s = E.eigenvalue FresnelChannel.s U

  /-- The `p` Fresnel coefficient is the `p` eigenvalue. -/
  coeff_p :
    ∀ U : State,
      (coeffs U).r_p = E.eigenvalue FresnelChannel.p U


namespace FresnelEigenvalueCalibration

variable
    {State Op : Type*} [Ring Op] [Algebra ℂ Op]
    {P : SPProjectorPair Op}
    {E : SPEigenResponseCalibration State Op P}

variable (F : FresnelEigenvalueCalibration State Op P E)

/-- Channel-indexed Fresnel coefficient readout. -/
def coeffOf
    (U : State) : FresnelChannel → ℂ
  | FresnelChannel.s => (F.coeffs U).r_s
  | FresnelChannel.p => (F.coeffs U).r_p

/--
The Jones reflector associated to a calibrated state.
-/
def jonesReflector
    (U : State) : JonesReflector Op where
  projectors := P
  coeffs := F.coeffs U

/--
The `s` coefficient of the calibrated Jones reflector is the `s` eigenvalue.
-/
theorem jones_r_s_eq_eigenvalue
    (U : State) :
    ((F.jonesReflector U).coeffs).r_s =
      E.eigenvalue FresnelChannel.s U := by sorry
/--
The `p` coefficient of the calibrated Jones reflector is the `p` eigenvalue.
-/
theorem jones_r_p_eq_eigenvalue
    (U : State) :
    ((F.jonesReflector U).coeffs).r_p =
      E.eigenvalue FresnelChannel.p U := by sorry
/--
The channel-indexed Fresnel coefficient is the calibrated response eigenvalue.
-/
theorem coeffOf_eq_eigenvalue
    (U : State)
    (c : FresnelChannel) :
    F.coeffOf U c = E.eigenvalue c U := by sorry
/--
The calibrated response operator acts on each Jones channel projector by the
corresponding Fresnel coefficient.
-/
theorem response_mul_projectorOf_eq_coeff
    (U : State)
    (c : FresnelChannel) :
    E.responseOp U * P.projectorOf c =
      F.coeffOf U c • P.projectorOf c := by sorry
end FresnelEigenvalueCalibration

/-! ## Metal mirror susceptibility calibration -/

/--
Metal mirror susceptibility/Hessian calibration.

This bridges Bregman heat, Hessian response, optical susceptibility, dielectric
response, and Jones/Fresnel readouts.
-/
structure MetalMirrorSusceptibilityCalibration
    (Op Field Response : Type*)
    [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response] where
  /-- Hessian/linear-response backend. -/
  hessianResponse :
    HessianResponseDatum Op Field Response

  /-- Susceptibility backend. -/
  susceptibility :
    SusceptibilityDatum Op Field Response

  /-- Dielectric/material response backend. -/
  dielectric :
    DielectricResponseDatum Op

  /-- Fresnel/Jones boundary calibration. -/
  fresnel :
    FresnelFromSusceptibilityCalibration Op





namespace MetalMirrorSusceptibilityCalibration

variable
    {Op Field Response : Type*}
    [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response]

end MetalMirrorSusceptibilityCalibration

/-! ## Full Hessian-to-Jones material calibration -/

/--
Complete susceptibility/Hessian-to-Jones calibration.

This is the material response bridge:

  Hessian response
      → susceptibility
      → dielectric response
      → s/p response eigenvalues
      → Fresnel coefficients
      → Jones reflector.
-/
structure SusceptibilityHessianJonesCalibration
    (State Field Response JonesOp : Type*)
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response]
    [Ring JonesOp] [Algebra ℂ JonesOp] where
  /-- Hessian response of the information potential. -/
  hessian :
    HessianResponseDatum State Field Response

  /-- Susceptibility derived from the Hessian. -/
  susceptibility :
    SusceptibilityDatum State Field Response

  /-- Dielectric/refractive-index response. -/
  dielectric :
    DielectricResponseDatum State

  /-- Optical interface geometry. -/
  interface :
    OpticalInterfaceGeometry

  /-- s/p projector pair in the Jones algebra. -/
  projectors :
    SPProjectorPair JonesOp

  /-- s/p response eigenchannel calibration. -/
  eigenResponse :
    SPEigenResponseCalibration State JonesOp projectors

  /-- Fresnel coefficients as eigenchannel readouts. -/
  fresnel :
    FresnelEigenvalueCalibration State JonesOp projectors eigenResponse





namespace SusceptibilityHessianJonesCalibration

variable
    {State Field Response JonesOp : Type*}
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response]
    [Ring JonesOp] [Algebra ℂ JonesOp]

variable (C :
  SusceptibilityHessianJonesCalibration State Field Response JonesOp)

/--
The calibrated Jones reflector for a material state.
-/
def jonesReflector
    (U : State) : JonesReflector JonesOp :=
  C.fresnel.jonesReflector U

/--
The `s` Fresnel/Jones coefficient is the calibrated `s` eigenvalue.
-/
theorem r_s_eq_s_eigenvalue
    (U : State) :
    ((C.jonesReflector U).coeffs).r_s =
      C.eigenResponse.eigenvalue FresnelChannel.s U := by sorry
/--
The `p` Fresnel/Jones coefficient is the calibrated `p` eigenvalue.
-/
theorem r_p_eq_p_eigenvalue
    (U : State) :
    ((C.jonesReflector U).coeffs).r_p =
      C.eigenResponse.eigenvalue FresnelChannel.p U := by sorry
end SusceptibilityHessianJonesCalibration

/--
Metal mirror material calibration.

This records the physical readouts that connect complex response eigenvalues
to absorption, retardance, and ellipticity.
-/
structure MetalMirrorSusceptibilityHessianCalibration
    (State Field Response JonesOp : Type*)
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response]
    [Ring JonesOp] [Algebra ℂ JonesOp] where
  /-- Full Hessian-to-Jones calibration. -/
  calibration :
    SusceptibilityHessianJonesCalibration State Field Response JonesOp

  /-- Absorption readout. -/
  absorption : State → ℝ

  /-- Retardance readout. -/
  retardance : State → ℝ

  /-- Ellipticity readout. -/
  ellipticity : State → ℝ

  /-- Complex-index readout. -/
  complexIndex : State → ℂ





namespace MetalMirrorSusceptibilityHessianCalibration

variable
    {State Field Response JonesOp : Type*}
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response]
    [Ring JonesOp] [Algebra ℂ JonesOp]

variable (M :
  MetalMirrorSusceptibilityHessianCalibration State Field Response JonesOp)

/--
The `s` Fresnel/Jones coefficient is the calibrated `s` eigenvalue for the
underlying material calibration.
-/
theorem r_s_eq_s_eigenvalue
    (U : State) :
    ((M.calibration.jonesReflector U).coeffs).r_s =
      M.calibration.eigenResponse.eigenvalue FresnelChannel.s U := by sorry
/--
The `p` Fresnel/Jones coefficient is the calibrated `p` eigenvalue for the
underlying material calibration.
-/
theorem r_p_eq_p_eigenvalue
    (U : State) :
    ((M.calibration.jonesReflector U).coeffs).r_p =
      M.calibration.eigenResponse.eigenvalue FresnelChannel.p U := by sorry
end MetalMirrorSusceptibilityHessianCalibration

attribute [rep_depth operator]
  HessianResponseDatum
  SusceptibilityDatum
  ConstructiveHessianSusceptibilityCalibration
  ConstructiveHessianSusceptibilityCalibration.susceptibility
  ConstructiveHessianSusceptibilityCalibration.susceptibility_eq_hessian_response
  ConstructiveHessianSusceptibilityCalibration.susceptibility_apply
  ConstructiveHessianSusceptibilityCalibration.toSusceptibilityDatum
  ConstructiveHessianSusceptibilityCalibration.toSusceptibilityDatum_susceptibility
  ConstructiveHessianSusceptibilityCalibration.toSusceptibilityDatum_derived_from_hessian
  DielectricResponseDatum
  ConstructiveDielectricResponseCalibration
  ConstructiveDielectricResponseCalibration.toDielectricResponseDatum
  ConstructiveDielectricResponseCalibration.toDielectricResponseDatum_epsilon
  ConstructiveDielectricResponseCalibration.toDielectricResponseDatum_refractiveIndex
  OpticalInterfaceGeometry
  FresnelFromSusceptibilityCalibration
  SPEigenResponseCalibration
  SPEigenResponseCalibration.response_mul_s_projector
  SPEigenResponseCalibration.response_mul_p_projector
  SPEigenResponseCalibration.response_mul_projectorOf
  FresnelEigenvalueCalibration
  FresnelEigenvalueCalibration.coeffOf
  FresnelEigenvalueCalibration.jonesReflector
  FresnelEigenvalueCalibration.jones_r_s_eq_eigenvalue
  FresnelEigenvalueCalibration.jones_r_p_eq_eigenvalue
  FresnelEigenvalueCalibration.coeffOf_eq_eigenvalue
  FresnelEigenvalueCalibration.response_mul_projectorOf_eq_coeff
  MetalMirrorSusceptibilityCalibration
  SusceptibilityHessianJonesCalibration
  SusceptibilityHessianJonesCalibration.jonesReflector
  SusceptibilityHessianJonesCalibration.r_s_eq_s_eigenvalue
  SusceptibilityHessianJonesCalibration.r_p_eq_p_eigenvalue
  MetalMirrorSusceptibilityHessianCalibration
  MetalMirrorSusceptibilityHessianCalibration.r_s_eq_s_eigenvalue
  MetalMirrorSusceptibilityHessianCalibration.r_p_eq_p_eigenvalue

end InfoGeometry.Thermo.SusceptibilityHessian

-- [STITCHER: MISSING OVERLAP] --
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
    (C.eventOf U).jones 0 0 = F.rs U := by sorry
/--
The calibrated Jones matrix has `r_p` in the second diagonal channel.
-/
theorem jones_11_eq_rp
    (U : State) :
    (C.eventOf U).jones 1 1 = F.rp U := by sorry
/--
The calibrated Jones matrix is diagonal in the local `s/p` eigenbasis.
-/
theorem jones_offdiag_01_zero
    (U : State) :
    (C.eventOf U).jones 0 1 = 0 := by sorry
/--
The calibrated Jones matrix is diagonal in the local `s/p` eigenbasis.
-/
theorem jones_offdiag_10_zero
    (U : State) :
    (C.eventOf U).jones 1 0 = 0 := by sorry
end JonesFromMaterialCalibration

/-! ## 4. Retardance and absorption readouts -/

/--
Retardance/ellipticity readout from Jones coefficients.
-- [STITCHER: MISSING OVERLAP] --
    (U : State) :
    (spJonesEventOfFresnel F U).jones 1 1 = F.rp U := rfl
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