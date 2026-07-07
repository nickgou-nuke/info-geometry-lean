import Mathlib
import InfoGeometry.OperatorAlgebra.SusceptibilityHessian.HessianResponse

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SusceptibilityHessian

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
