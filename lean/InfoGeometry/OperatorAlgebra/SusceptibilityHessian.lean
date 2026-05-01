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

  /-- Transmission/interface law certificate. -/
  transmissionBoundaryLaw : Prop

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

  /-- Certificate for the operatorial implementation of boundary response. -/
  operatorialBoundaryLaw : Prop

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
  MaterialSusceptibilityHessianCompatibility
  MaterialSusceptibilityHessianOwnerTarget
  SusceptibilityHessianOwnerTarget
  susceptibilityHessianOwnerTarget

end InfoGeometry.OperatorAlgebra.SusceptibilityHessian
