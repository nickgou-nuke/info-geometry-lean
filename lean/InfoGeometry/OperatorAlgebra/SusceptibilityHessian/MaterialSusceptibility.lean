import Mathlib.Tactic
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

  /--
  Linear isotropic material relation between complex refractive index and
  susceptibility.
  -/
  index_sq_eq_one_add_susceptibility :
    ∀ U : State, complexIndex U ^ (2 : ℕ) = 1 + susceptibility U

namespace MaterialResponseModel

variable {State : Type*}
variable (M : MaterialResponseModel State)

/-- The refractive-index readout is tied to susceptibility by the material law. -/
theorem index_sq_eq_one_add_susceptibility_apply
    (U : State) :
    M.complexIndex U ^ (2 : ℕ) = 1 + M.susceptibility U :=
  M.index_sq_eq_one_add_susceptibility U

end MaterialResponseModel

/--
Calibration saying the Hessian response produces the material susceptibility.

This is model-dependent and therefore proof-carrying.
-/
structure HessianSusceptibilityCalibration
    (State : Type*) [NormedAddCommGroup State] [NormedSpace ℝ State]
    (H : HessianResponseDatum State)
    (M : MaterialResponseModel State) where
  /-- Complex susceptibility readout induced by the Hessian response. -/
  susceptibilityFromHessian : State → ℂ

  /-- The material susceptibility is exactly the Hessian-induced readout. -/
  susceptibility_eq_hessian_readout :
    ∀ U : State, M.susceptibility U = susceptibilityFromHessian U

  /-- Regular states have nonzero complex refractive-index readout. -/
  regular_complex_index_ne_zero :
    ∀ U : State, H.regularAt U → M.complexIndex U ≠ 0

namespace HessianSusceptibilityCalibration

variable {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]
variable {H : HessianResponseDatum State}
variable {M : MaterialResponseModel State}
variable (C : HessianSusceptibilityCalibration State H M)

/-- The material susceptibility is the Hessian-induced readout. -/
theorem susceptibility_eq_hessian_readout_apply
    (U : State) :
    M.susceptibility U = C.susceptibilityFromHessian U :=
  C.susceptibility_eq_hessian_readout U

/-- Regular states have nonzero complex refractive-index readout. -/
theorem complexIndex_ne_zero_of_regular
    (C : HessianSusceptibilityCalibration State H M)
    {U : State}
    (hU : H.regularAt U) :
    M.complexIndex U ≠ 0 :=
  match C with
  | ⟨_, _, hregular⟩ => hregular U hU

end HessianSusceptibilityCalibration
