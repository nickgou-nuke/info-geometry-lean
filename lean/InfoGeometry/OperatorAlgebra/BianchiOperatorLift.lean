import Mathlib

namespace InfoGeometry.OperatorAlgebra

/-!
Algebraic Bianchi identities in an associative envelope.

This owner deliberately stops at the associative commutator calculus.  It does
not package differential forms, a connection, or a curvature hypothesis as
structure fields.  Those require a separate representation and differential
calculus.  The theorem below is the native algebraic identity available in any
associative ring.
-/

variable {A : Type*} [Ring A]

/-- The associative-envelope commutator readout. -/
def associativeCommutator (x y : A) : A := x * y - y * x

/-- The cyclic, right-nested commutator expression. -/
def bianchiJacobiator (x y z : A) : A :=
  associativeCommutator x (associativeCommutator y z) +
    associativeCommutator y (associativeCommutator z x) +
    associativeCommutator z (associativeCommutator x y)

/-- The cyclic, left-nested commutator expression. -/
def leftJacobiator (x y z : A) : A :=
  associativeCommutator (associativeCommutator x y) z +
    associativeCommutator (associativeCommutator y z) x +
    associativeCommutator (associativeCommutator z x) y

/-- The associative commutator satisfies the Jacobi/Bianchi identity. -/
theorem bianchiJacobiator_eq_zero (x y z : A) :
  bianchiJacobiator x y z = 0 := by
  unfold bianchiJacobiator associativeCommutator
  noncomm_ring

/-- The left-nested associative commutator also satisfies Jacobi. -/
theorem leftJacobiator_eq_zero (x y z : A) :
    leftJacobiator x y z = 0 := by
  unfold leftJacobiator associativeCommutator
  noncomm_ring

/-- The two cyclic Jacobiator conventions differ by a sign. -/
theorem leftJacobiator_eq_neg_bianchiJacobiator (x y z : A) :
    leftJacobiator x y z = -bianchiJacobiator x y z := by
  unfold leftJacobiator bianchiJacobiator associativeCommutator
  noncomm_ring

/-- The commutator is antisymmetric. -/
theorem associativeCommutator_swap (x y : A) :
    associativeCommutator y x = -associativeCommutator x y := by
  unfold associativeCommutator
  noncomm_ring

end InfoGeometry.OperatorAlgebra
