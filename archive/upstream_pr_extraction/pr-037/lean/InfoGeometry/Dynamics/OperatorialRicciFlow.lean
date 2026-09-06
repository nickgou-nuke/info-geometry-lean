import Mathlib.Tactic

/-!
# InfoGeometry.Dynamics.OperatorialRicciFlow

A finite algebraic subtraction-step readout.  It is not a Ricci-flow or
curvature construction; those require a connection and a geometric carrier.
-/

noncomputable section

namespace InfoGeometry.Dynamics.OperatorialRicciFlow

/-- One explicit subtraction step on a carrier with a subtraction operation. -/
def subtractionStep {E : Type*} [Sub E] (x v : E) : E :=
  x - v

/-- The finite step is definitionally subtraction by its supplied increment. -/
theorem subtractionStep_eq {E : Type*} [Sub E] (x v : E) :
    subtractionStep x v = x - v := by
  rfl

end InfoGeometry.Dynamics.OperatorialRicciFlow
