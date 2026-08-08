/-
InfoGeometry/Optics/OperatorValuedConnection.lean

Algebraic connection and curvature for operator-valued polarization forms.

This is deliberately independent of a manifold implementation.  The existing
`OperatorOneForm` owner supplies the one-form shape; this file adds the
noncommutative wedge-square and an explicitly antisymmetric derivative datum.
-/

import Mathlib.Tactic
import InfoGeometry.Geometry.BilingualAnalyticity

noncomputable section

namespace InfoGeometry.Optics.OperatorValuedConnection

open InfoGeometry.Geometry.BilingualAnalyticity

variable {Point Tangent Value : Type*}
variable [Ring Value] [Algebra ℝ Value]

/-- The commutator wedge square of an operator-valued one-form.

For tangent directions `X` and `Y` this is
`Ω(X) Ω(Y) - Ω(Y) Ω(X)`.  No commutativity of the value algebra is assumed.
-/
def wedgeSquare
    (ω : OperatorOneForm Point Tangent Value)
    (p : Point) (X Y : Tangent) : Value :=
  ω p X * ω p Y - ω p Y * ω p X

@[simp]
theorem wedgeSquare_swap
    (ω : OperatorOneForm Point Tangent Value)
    (p : Point) (X Y : Tangent) :
    wedgeSquare ω p Y X = -wedgeSquare ω p X Y := by
  unfold wedgeSquare
  noncomm_ring

/-- An algebraic operator-valued connection datum.

`derivative` is the exterior/geometric derivative contribution.  Its
antisymmetry is stored explicitly so this structure can be used with the
repository's abstract geometric-derivative backends without asserting a
stronger manifold theorem than the backend provides.
-/
structure Connection where
  form : OperatorOneForm Point Tangent Value
  derivative : Point → Tangent → Tangent → Value
  derivative_swap :
    ∀ p X Y, derivative p Y X = -derivative p X Y
  derivative_same :
    ∀ p X, derivative p X X = 0

/-- Curvature `F = dΩ + Ω ∧ Ω` in the algebraic operator-valued model. -/
def curvature (C : Connection (Point := Point) (Tangent := Tangent) (Value := Value))
    (p : Point) (X Y : Tangent) : Value :=
  C.derivative p X Y + wedgeSquare C.form p X Y

@[simp]
theorem curvature_swap
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := Value))
    (p : Point) (X Y : Tangent) :
    curvature C p Y X = -curvature C p X Y := by
  unfold curvature
  rw [C.derivative_swap, wedgeSquare_swap]
  simp only [neg_add]

@[simp]
theorem curvature_same
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := Value))
    (p : Point) (X : Tangent) :
    curvature C p X X = 0 := by
  unfold curvature wedgeSquare
  rw [C.derivative_same]
  simp

/-- The flatness predicate for the algebraic connection datum. -/
def IsFlat
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := Value)) : Prop :=
  ∀ p X Y, curvature C p X Y = 0

theorem curvature_eq_zero_of_flat
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := Value))
    (hflat : IsFlat C) (p : Point) (X Y : Tangent) :
    curvature C p X Y = 0 :=
  hflat p X Y

end InfoGeometry.Optics.OperatorValuedConnection
