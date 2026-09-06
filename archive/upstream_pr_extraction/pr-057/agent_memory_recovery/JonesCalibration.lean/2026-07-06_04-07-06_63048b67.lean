/--
Finite Jones optical event.

This is the compatibility event surface used by the finite operator-algebra
readouts. The diagonal matrix is computed from the two event coefficients.
-/
structure JonesOpticalEvent where
  basis : PolarizationBasis
  kind : OpticalSurfaceKind
  coeff0 : ℂ
  coeff1 : ℂ
  tag : V4Tag
  coherence : Prop

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
def jones (E : JonesOpticalEvent) : JonesMat :=
  diagJones E.coeff0 E.coeff1

@[simp]
theorem jones_apply_same_zero (E : JonesOpticalEvent) :
    E.jones 0 0 = E.coeff0 := by