import Mathlib
import InfoGeometry.Optics.JonesCalibration
import InfoGeometry.OperatorAlgebra.StinespringDilation
import InfoGeometry.OperatorAlgebra.SusceptibilityHessian.MaterialSusceptibility

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SusceptibilityHessian

open JonesCalibration
open StinespringDilation

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
  coherence :=
    diagJones (F.rs U) (F.rp U) 0 1 = 0 ∧
      diagJones (F.rs U) (F.rp U) 1 0 = 0

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

/-- The canonical Fresnel/Jones event is coherently diagonal. -/
theorem spJonesEventOfFresnel_coherence
    {State : Type*}
    (F : FresnelCoefficientReadout State)
    (U : State) :
    (spJonesEventOfFresnel F U).coherence := by
  simp [spJonesEventOfFresnel, diagJones]

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
