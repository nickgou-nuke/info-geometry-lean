import Mathlib
import InfoGeometry.Thermo.MetalMirror
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

/-! ## Owner target -/

/--
Owner target for installing a Hessian-to-susceptibility optical calibration.
-/
def SusceptibilityHessianOwnerTarget
    (Op Field Response : Type*)
    [NormedAddCommGroup Op] [NormedSpace ℝ Op]
    [NormedAddCommGroup Field] [NormedSpace ℝ Field]
    [NormedAddCommGroup Response] [NormedSpace ℝ Response] : Prop :=
  Nonempty
    (MetalMirrorSusceptibilityCalibration Op Field Response)

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
  MetalMirrorSusceptibilityCalibration
  MetalMirrorSusceptibilityCalibration.hessian_controls_susceptibility_valid
  MetalMirrorSusceptibilityCalibration.susceptibility_controls_absorption_valid
  MetalMirrorSusceptibilityCalibration.susceptibility_controls_retardance_valid
  MetalMirrorSusceptibilityCalibration.jones_calibrated_valid
  MetalMirrorSusceptibilityCalibration.fresnel_coefficients_certified
  SusceptibilityHessianOwnerTarget

end InfoGeometry.Thermo.SusceptibilityHessian

