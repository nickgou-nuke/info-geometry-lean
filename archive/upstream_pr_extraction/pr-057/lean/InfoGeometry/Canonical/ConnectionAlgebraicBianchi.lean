import InfoGeometry.Algebra.AkivisIdentity
import InfoGeometry.Optics.OperatorValuedConnection

/-!
# Algebraic Bianchi readout for operator-valued connections

This owner deliberately stays below differential-form Yang--Mills theory.  It
records the cyclic right-nested commutator of the connection one-form and
identifies it with the generic Akivis Jacobiator.  Since the value type of the
repository `Connection` is an associative `Ring`, that ambient cyclic
expression vanishes.  Nonzero projected shadows are handled by the separate
Akivis/leakage owners.
-/

noncomputable section

namespace InfoGeometry.Canonical.ConnectionAlgebraicBianchi

open InfoGeometry.Algebra
open InfoGeometry.Optics.OperatorValuedConnection

variable {Point Tangent Value : Type*} [Ring Value]

/-- The right-nested cyclic commutator of a connection one-form. -/
def rightNestedBianchi
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := Value))
    (p : Point) (X Y Z : Tangent) : Value :=
  rightNestedJacobiator (C.form p X) (C.form p Y) (C.form p Z)

theorem rightNestedBianchi_eq_neg_jacobiator
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := Value))
    (p : Point) (X Y Z : Tangent) :
    rightNestedBianchi C p X Y Z =
      -akivisJacobiator (C.form p X) (C.form p Y) (C.form p Z) := by
  exact rightNestedJacobiator_eq_neg _ _ _

/-- In the associative operator envelope, the cyclic commutator vanishes. -/
theorem rightNestedBianchi_eq_zero
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := Value))
    (p : Point) (X Y Z : Tangent) :
    rightNestedBianchi C p X Y Z = 0 := by
  simp [rightNestedBianchi, rightNestedJacobiator, akivisBracket]
  noncomm_ring

end InfoGeometry.Canonical.ConnectionAlgebraicBianchi
