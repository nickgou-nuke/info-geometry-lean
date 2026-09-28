import Mathlib.Algebra.Ring.Associator
variable {A : Type*} [NonUnitalNonAssocRing A]
def akivisBracket (x y : A) : A := x * y - y * x
def leftMultiplication (x z : A) : A := x * z
def leftMultiplicationCommutatorDefect (x y z : A) : A :=
  leftMultiplication x (leftMultiplication y z) - leftMultiplication y (leftMultiplication x z) - leftMultiplication (akivisBracket x y) z

theorem leftMultiplicationCommutatorDefect_eq_associator_difference
    (x y z : A) :
    leftMultiplicationCommutatorDefect x y z =
      -_root_.associator x y z + _root_.associator y x z := by
  simp only [leftMultiplicationCommutatorDefect, leftMultiplication,
    akivisBracket, _root_.associator_apply, sub_mul, mul_sub]
  abel
