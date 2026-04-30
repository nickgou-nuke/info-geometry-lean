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

  /-- Law that this Hessian is the intended linear-response geometry. -/
  hessian_response_law : Prop

  /-- Evidence that this Hessian is the intended linear-response geometry. -/
  hessian_response_certificate :
    hessian_response_law

namespace HessianResponseDatum

variable
    {Op Field Response : Type*}
    [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response]

variable (H : HessianResponseDatum Op Field Response)

/-- Re-export of the Hessian/linear-response certificate. -/
theorem hessian_response_valid :
    H.hessian_response_law :=
  H.hessian_response_certificate

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

  /-- Law that susceptibility is obtained from the Hessian response. -/
  derived_from_hessian_law : Prop

  /-- Evidence that susceptibility is obtained from the Hessian response. -/
  derived_from_hessian :
    derived_from_hessian_law

namespace SusceptibilityDatum

variable
    {Op Field Response : Type*}
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response]

variable (S : SusceptibilityDatum Op Field Response)

/-- Re-export of the susceptibility-from-Hessian certificate. -/
theorem derived_from_hessian_valid :
    S.derived_from_hessian_law :=
  S.derived_from_hessian

end SusceptibilityDatum

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

  /--
  Calibration law, e.g. `N² = εᵣ μᵣ`, or `N² = εᵣ` in a nonmagnetic model.
  -/
  refractive_index_calibration_law : Prop

  /-- Evidence for the refractive-index calibration law. -/
  refractive_index_calibration :
    refractive_index_calibration_law

  /-- Law connecting susceptibility to dielectric response. -/
  susceptibility_to_epsilon_law : Prop

  /-- Evidence connecting susceptibility to dielectric response. -/
  susceptibility_to_epsilon :
    susceptibility_to_epsilon_law

namespace DielectricResponseDatum

variable {Op : Type*}
variable (D : DielectricResponseDatum Op)

/-- Re-export of the refractive-index calibration law. -/
theorem refractive_index_calibration_valid :
    D.refractive_index_calibration_law :=
  D.refractive_index_calibration

/-- Re-export of the susceptibility-to-dielectric calibration law. -/
theorem susceptibility_to_epsilon_valid :
    D.susceptibility_to_epsilon_law :=
  D.susceptibility_to_epsilon

end DielectricResponseDatum

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

  /-- Geometric/Snell-law calibration law. -/
  angle_calibration_law : Prop

  /-- Evidence for the geometric/Snell-law calibration. -/
  angle_calibration :
    angle_calibration_law

namespace OpticalInterfaceGeometry

variable (G : OpticalInterfaceGeometry)

/-- Re-export of the interface angle calibration law. -/
theorem angle_calibration_valid :
    G.angle_calibration_law :=
  G.angle_calibration

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

  /--
  Law that `coeffs.r_s` and `coeffs.r_p` are the Fresnel coefficients
  determined by `dielectric` and `interfaceGeometry`.
  -/
  fresnel_from_dielectric_law : Prop

  /-- Evidence for the Fresnel-from-dielectric law. -/
  fresnel_from_dielectric :
    fresnel_from_dielectric_law

namespace FresnelFromSusceptibilityCalibration

variable {Op : Type*}
variable (F : FresnelFromSusceptibilityCalibration Op)

/-- Re-export of the Fresnel-from-dielectric calibration law. -/
theorem fresnel_from_dielectric_valid :
    F.fresnel_from_dielectric_law :=
  F.fresnel_from_dielectric

/-- Re-export of the Jones-layer Fresnel law carried by the coefficients. -/
theorem coeffs_fresnel_valid :
    F.coeffs.fresnel_law :=
  F.coeffs.fresnel_certificate

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

  /-- Law that the eigenvalues come from the intended Fresnel boundary problem. -/
  fresnel_boundary_calibration_law : Prop

  /-- Evidence that the eigenvalues come from the intended Fresnel boundary problem. -/
  fresnel_boundary_calibration :
    fresnel_boundary_calibration_law

namespace FresnelEigenvalueCalibration

variable
    {State Op : Type*} [Ring Op] [Algebra ℂ Op]
    {P : SPProjectorPair Op}
    {E : SPEigenResponseCalibration State Op P}

variable (F : FresnelEigenvalueCalibration State Op P E)

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

/-- Re-export of the Fresnel boundary calibration certificate. -/
theorem fresnel_boundary_calibration_valid :
    F.fresnel_boundary_calibration_law :=
  F.fresnel_boundary_calibration

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

  /-- Law that Hessian response determines susceptibility in this model. -/
  hessian_controls_susceptibility_law : Prop

  /-- Evidence that Hessian response determines susceptibility. -/
  hessian_controls_susceptibility :
    hessian_controls_susceptibility_law

  /-- Law that susceptibility/dielectric response controls absorption. -/
  susceptibility_controls_absorption_law : Prop

  /-- Evidence that susceptibility/dielectric response controls absorption. -/
  susceptibility_controls_absorption :
    susceptibility_controls_absorption_law

  /-- Law that susceptibility/dielectric response controls retardance. -/
  susceptibility_controls_retardance_law : Prop

  /-- Evidence that susceptibility/dielectric response controls retardance. -/
  susceptibility_controls_retardance :
    susceptibility_controls_retardance_law

  /-- Law that the Jones reflector is calibrated by the Fresnel coefficients. -/
  jones_calibrated_law : Prop

  /-- Evidence that the Jones reflector is calibrated by the Fresnel coefficients. -/
  jones_calibrated :
    jones_calibrated_law

namespace MetalMirrorSusceptibilityCalibration

variable
    {Op Field Response : Type*}
    [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response]

variable (M : MetalMirrorSusceptibilityCalibration Op Field Response)

/-- Re-export of Hessian-to-susceptibility control. -/
theorem hessian_controls_susceptibility_valid :
    M.hessian_controls_susceptibility_law :=
  M.hessian_controls_susceptibility

/-- Re-export of susceptibility/dielectric absorption control. -/
theorem susceptibility_controls_absorption_valid :
    M.susceptibility_controls_absorption_law :=
  M.susceptibility_controls_absorption

/-- Re-export of susceptibility/dielectric retardance control. -/
theorem susceptibility_controls_retardance_valid :
    M.susceptibility_controls_retardance_law :=
  M.susceptibility_controls_retardance

/-- Re-export of the Jones/Fresnel calibration. -/
theorem jones_calibrated_valid :
    M.jones_calibrated_law :=
  M.jones_calibrated

/--
The installed Fresnel coefficients carry the Jones-layer Fresnel certificate.
-/
theorem fresnel_coefficients_certified :
    M.fresnel.coeffs.fresnel_law :=
  M.fresnel.coeffs_fresnel_valid

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
  hessian_controls_susceptibility_law : Prop

  /-- Evidence that Hessian response controls susceptibility. -/
  hessian_controls_susceptibility :
    hessian_controls_susceptibility_law

  /-- Susceptibility controls dielectric response. -/
  susceptibility_controls_dielectric_law : Prop

  /-- Evidence that susceptibility controls dielectric response. -/
  susceptibility_controls_dielectric :
    susceptibility_controls_dielectric_law

  /-- Dielectric response plus interface geometry controls Fresnel coefficients. -/
  dielectric_controls_fresnel_law : Prop

  /-- Evidence that dielectric response plus interface geometry controls Fresnel coefficients. -/
  dielectric_controls_fresnel :
    dielectric_controls_fresnel_law

  /-- Jones reflector is calibrated by the resulting Fresnel coefficients. -/
  jones_calibrated_law : Prop

  /-- Evidence that the Jones reflector is calibrated by the Fresnel coefficients. -/
  jones_calibrated :
    jones_calibrated_law

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

/-- Re-export of Hessian-to-susceptibility calibration. -/
theorem hessian_controls_susceptibility_valid :
    C.hessian_controls_susceptibility_law :=
  C.hessian_controls_susceptibility

/-- Re-export of susceptibility-to-dielectric calibration. -/
theorem susceptibility_controls_dielectric_valid :
    C.susceptibility_controls_dielectric_law :=
  C.susceptibility_controls_dielectric

/-- Re-export of dielectric/interface-to-Fresnel calibration. -/
theorem dielectric_controls_fresnel_valid :
    C.dielectric_controls_fresnel_law :=
  C.dielectric_controls_fresnel

/-- Re-export of Jones reflector calibration. -/
theorem jones_calibrated_valid :
    C.jones_calibrated_law :=
  C.jones_calibrated

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

  /-- Law that absorption is controlled by the dissipative part of response. -/
  response_controls_absorption_law : Prop

  /-- Evidence that absorption is controlled by the dissipative part of response. -/
  response_controls_absorption :
    response_controls_absorption_law

  /-- Law that retardance is controlled by relative phase of `s/p` eigenvalues. -/
  eigenphase_controls_retardance_law : Prop

  /-- Evidence that retardance is controlled by relative phase of `s/p` eigenvalues. -/
  eigenphase_controls_retardance :
    eigenphase_controls_retardance_law

  /-- Law that ellipticity is controlled by amplitude imbalance plus retardance. -/
  eigenresponse_controls_ellipticity_law : Prop

  /-- Evidence that ellipticity is controlled by amplitude imbalance plus retardance. -/
  eigenresponse_controls_ellipticity :
    eigenresponse_controls_ellipticity_law

  /-- Law that complex index is calibrated to the dielectric response. -/
  complex_index_calibrated_law : Prop

  /-- Evidence that complex index is calibrated to the dielectric response. -/
  complex_index_calibrated :
    complex_index_calibrated_law

namespace MetalMirrorSusceptibilityHessianCalibration

variable
    {State Field Response JonesOp : Type*}
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response]
    [Ring JonesOp] [Algebra ℂ JonesOp]

variable (M :
  MetalMirrorSusceptibilityHessianCalibration State Field Response JonesOp)

/-- Re-export of response-to-absorption calibration. -/
theorem response_controls_absorption_valid :
    M.response_controls_absorption_law :=
  M.response_controls_absorption

/-- Re-export of eigenphase-to-retardance calibration. -/
theorem eigenphase_controls_retardance_valid :
    M.eigenphase_controls_retardance_law :=
  M.eigenphase_controls_retardance

/-- Re-export of eigenresponse-to-ellipticity calibration. -/
theorem eigenresponse_controls_ellipticity_valid :
    M.eigenresponse_controls_ellipticity_law :=
  M.eigenresponse_controls_ellipticity

/-- Re-export of complex-index calibration. -/
theorem complex_index_calibrated_valid :
    M.complex_index_calibrated_law :=
  M.complex_index_calibrated

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

/-! ## Owner target -/

/--
Owner target for installing the generic Hessian-to-susceptibility metal mirror
calibration.
-/
def MetalMirrorSusceptibilityCalibrationOwnerTarget
    (Op Field Response : Type*)
    [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response] : Prop :=
  Nonempty
    (MetalMirrorSusceptibilityCalibration Op Field Response)

/--
Owner target for a Hessian-to-Fresnel/Jones calibration.
-/
def SusceptibilityHessianOwnerTarget
    (State Field Response JonesOp : Type*)
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response]
    [Ring JonesOp] [Algebra ℂ JonesOp] : Prop :=
  Nonempty
    (SusceptibilityHessianJonesCalibration State Field Response JonesOp)

/--
Owner target for a metal mirror material calibration.
-/
def MetalMirrorSusceptibilityHessianOwnerTarget
    (State Field Response JonesOp : Type*)
    [NormedAddCommGroup State] [NormedSpace ℝ State]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response]
    [Ring JonesOp] [Algebra ℂ JonesOp] : Prop :=
  Nonempty
    (MetalMirrorSusceptibilityHessianCalibration State Field Response JonesOp)

attribute [rep_depth operator]
  HessianResponseDatum
  HessianResponseDatum.hessian_response_valid
  SusceptibilityDatum
  SusceptibilityDatum.derived_from_hessian_valid
  DielectricResponseDatum
  DielectricResponseDatum.refractive_index_calibration_valid
  DielectricResponseDatum.susceptibility_to_epsilon_valid
  OpticalInterfaceGeometry
  OpticalInterfaceGeometry.angle_calibration_valid
  FresnelFromSusceptibilityCalibration
  FresnelFromSusceptibilityCalibration.fresnel_from_dielectric_valid
  FresnelFromSusceptibilityCalibration.coeffs_fresnel_valid
  SPEigenResponseCalibration
  SPEigenResponseCalibration.response_mul_s_projector
  SPEigenResponseCalibration.response_mul_p_projector
  FresnelEigenvalueCalibration
  FresnelEigenvalueCalibration.jonesReflector
  FresnelEigenvalueCalibration.jones_r_s_eq_eigenvalue
  FresnelEigenvalueCalibration.jones_r_p_eq_eigenvalue
  FresnelEigenvalueCalibration.fresnel_boundary_calibration_valid
  MetalMirrorSusceptibilityCalibration
  MetalMirrorSusceptibilityCalibration.hessian_controls_susceptibility_valid
  MetalMirrorSusceptibilityCalibration.susceptibility_controls_absorption_valid
  MetalMirrorSusceptibilityCalibration.susceptibility_controls_retardance_valid
  MetalMirrorSusceptibilityCalibration.jones_calibrated_valid
  MetalMirrorSusceptibilityCalibration.fresnel_coefficients_certified
  SusceptibilityHessianJonesCalibration
  SusceptibilityHessianJonesCalibration.jonesReflector
  SusceptibilityHessianJonesCalibration.r_s_eq_s_eigenvalue
  SusceptibilityHessianJonesCalibration.r_p_eq_p_eigenvalue
  SusceptibilityHessianJonesCalibration.hessian_controls_susceptibility_valid
  SusceptibilityHessianJonesCalibration.susceptibility_controls_dielectric_valid
  SusceptibilityHessianJonesCalibration.dielectric_controls_fresnel_valid
  SusceptibilityHessianJonesCalibration.jones_calibrated_valid
  MetalMirrorSusceptibilityHessianCalibration
  MetalMirrorSusceptibilityHessianCalibration.response_controls_absorption_valid
  MetalMirrorSusceptibilityHessianCalibration.eigenphase_controls_retardance_valid
  MetalMirrorSusceptibilityHessianCalibration.eigenresponse_controls_ellipticity_valid
  MetalMirrorSusceptibilityHessianCalibration.complex_index_calibrated_valid
  MetalMirrorSusceptibilityHessianCalibration.r_s_eq_s_eigenvalue
  MetalMirrorSusceptibilityHessianCalibration.r_p_eq_p_eigenvalue
  MetalMirrorSusceptibilityCalibrationOwnerTarget
  SusceptibilityHessianOwnerTarget
  MetalMirrorSusceptibilityHessianOwnerTarget

end InfoGeometry.Thermo.SusceptibilityHessian
