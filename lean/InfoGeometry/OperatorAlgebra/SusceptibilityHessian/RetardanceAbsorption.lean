import Mathlib
import InfoGeometry.Optics.JonesCalibration
import InfoGeometry.OperatorAlgebra.SusceptibilityHessian.FresnelJones

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SusceptibilityHessian

open InfoGeometry.Optics.JonesCalibration

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

/--
Construct a full optical-response calibration using the canonical `s/p` Jones
event induced by Fresnel coefficients.

This eliminates the explicit Jones-event hypotheses in the coherent Fresnel
lane.  The remaining analytic/material calibrations are carried by the concrete
Hessian susceptibility, retardance, and absorption readouts themselves.
-/
def OpticalResponseCalibration.ofFresnel
    {State : Type*} [NormedAddCommGroup State] [NormedSpace ℝ State]
    {H : HessianResponseDatum State}
    {M : MaterialResponseModel State}
    {F : FresnelCoefficientReadout State}
    (hessianSusceptibility : HessianSusceptibilityCalibration State H M)
    (retardance : RetardanceReadout State)
    (absorption : OpticalAbsorptionReadout State) :
    OpticalResponseCalibration State H M F where
  hessianSusceptibility := hessianSusceptibility
  jonesCalibration := jonesFromMaterialCalibrationOfFresnel M F
  retardance := retardance
  absorption := absorption

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
