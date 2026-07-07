import Mathlib
import InfoGeometry.Optics.JonesCalibration
import InfoGeometry.Geometry.OpticalJonesV4
import InfoGeometry.Optics.FiniteJonesModel

namespace InfoGeometry.OperatorAlgebra.JonesCalibration

/--
Finite Jones optical event.

This is the compatibility event surface used by the finite operator-algebra
readouts. The diagonal matrix is computed from the two event coefficients.
-/
structure JonesOpticalEvent where
  basis : InfoGeometry.Optics.JonesCalibration.PolarizationBasis
  kind : InfoGeometry.Optics.JonesCalibration.OpticalSurfaceKind
  coeff0 : ℂ
  coeff1 : ℂ
  tag : InfoGeometry.Optics.JonesCalibration.V4Tag

/-- Instantiation of JonesOpticalEvent to prove it is non-vacuous. -/
def defaultJonesOpticalEvent : JonesOpticalEvent := {
  basis := InfoGeometry.Optics.JonesCalibration.PolarizationBasis.sp
  kind := InfoGeometry.Optics.JonesCalibration.OpticalSurfaceKind.abstract_
  coeff0 := 1
  coeff1 := 1
  tag := InfoGeometry.Optics.JonesCalibration.V4Tag.id
}

namespace JonesOpticalEvent

/-- First channel coefficient. -/
def firstCoeff (E : JonesOpticalEvent) : ℂ :=
  E.coeff0

/-- Second channel coefficient. -/
def secondCoeff (E : JonesOpticalEvent) : ℂ :=
  E.coeff1

@[simp]
theorem firstCoeff_eq (E : JonesOpticalEvent) :
    E.firstCoeff = E.coeff0 :=
  rfl

@[simp]
theorem secondCoeff_eq (E : JonesOpticalEvent) :
    E.secondCoeff = E.coeff1 :=
  rfl

/-- The diagonal Jones matrix associated to an event. -/
def jones (E : JonesOpticalEvent) : InfoGeometry.Optics.FiniteJonesModel.JonesMat :=
  InfoGeometry.Optics.FiniteJonesModel.diagJones E.coeff0 E.coeff1

@[simp]
theorem jones_apply_same_zero (E : JonesOpticalEvent) :
    E.jones 0 0 = E.coeff0 := by
  sorry

@[simp]
theorem jones_apply_same_one (E : JonesOpticalEvent) :
    E.jones 1 1 = E.coeff1 := by
  sorry

@[simp]
theorem jones_apply_offdiag_zero_one (E : JonesOpticalEvent) :
    E.jones 0 1 = 0 := by
  sorry

@[simp]
theorem jones_apply_offdiag_one_zero (E : JonesOpticalEvent) :
    E.jones 1 0 = 0 := by
  sorry

end JonesOpticalEvent

/--
Missing Jones calibration theorem.
Original recovered code was a vacuous `True := by trivial`.
-/
theorem jonesCalibration : False := by
  sorry

end InfoGeometry.OperatorAlgebra.JonesCalibration
