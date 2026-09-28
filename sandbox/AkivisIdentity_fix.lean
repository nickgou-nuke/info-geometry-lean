import Mathlib.Algebra.Ring.Associator

namespace InfoGeometry.Algebra

variable {A : Type*} [NonUnitalNonAssocRing A]

def akivisBracket (x y : A) : A := x * y - y * x

def akivisJacobiator (x y z : A) : A :=
  akivisBracket (akivisBracket x y) z +
    akivisBracket (akivisBracket y z) x +
      akivisBracket (akivisBracket z x) y

theorem akivis_identity (x y z : A) :
    akivisJacobiator x y z =
      _root_.associator x y z + _root_.associator y z x +
        _root_.associator z x y - _root_.associator y x z -
          _root_.associator z y x - _root_.associator x z y := by
  simp only [akivisJacobiator, akivisBracket, _root_.associator_apply, sub_mul, mul_sub]
  abel

end InfoGeometry.Algebra
