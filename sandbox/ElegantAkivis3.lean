import Mathlib.Algebra.Ring.Associator
variable {A : Type*} [NonUnitalNonAssocRing A]
def akivisBracket (x y : A) : A := x * y - y * x
def akivisJacobiator (x y z : A) : A :=
  akivisBracket (akivisBracket x y) z +
    akivisBracket (akivisBracket y z) x +
      akivisBracket (akivisBracket z x) y

lemma akivisBracket_akivisBracket (x y z : A) :
    akivisBracket (akivisBracket x y) z =
      _root_.associator x y z - _root_.associator y x z + x * (y * z) - y * (x * z) - z * (x * y) + z * (y * x) := by
  simp only [akivisBracket, _root_.associator_apply, sub_mul, mul_sub, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

theorem akivis_identity (x y z : A) :
    akivisJacobiator x y z =
      _root_.associator x y z + _root_.associator y z x +
        _root_.associator z x y - _root_.associator y x z -
          _root_.associator z y x - _root_.associator x z y := by
  dsimp [akivisJacobiator]
  rw [akivisBracket_akivisBracket x y z]
  rw [akivisBracket_akivisBracket y z x]
  rw [akivisBracket_akivisBracket z x y]
  simp only [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
