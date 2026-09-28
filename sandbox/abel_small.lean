import Mathlib.Algebra.Ring.Associator
variable {A : Type*} [NonUnitalNonAssocRing A]
def akivisBracket (x y : A) : A := x * y - y * x
lemma akivisBracket_akivisBracket (x y z : A) :
    akivisBracket (akivisBracket x y) z =
      _root_.associator x y z - _root_.associator y x z + x * (y * z) - y * (x * z) - z * (x * y) + z * (y * x) := by
  dsimp [akivisBracket, _root_.associator_apply]
  rw [sub_mul, mul_sub]
  abel
