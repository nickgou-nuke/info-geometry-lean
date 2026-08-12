import Mathlib.Algebra.Module.Basic

structure MyAlgebra where
  carrier : Type
  mul : carrier → carrier → carrier
  one : carrier

def my_iota (A : MyAlgebra) (i : Nat) : MyAlgebra :=
  A

def use_carrier (A : MyAlgebra) (x : A.carrier) : A.carrier :=
  x

theorem test_error (A : MyAlgebra) (i : Nat) :
  use_carrier A (my_iota A i) = A.carrier := by
  sorry

/--
Let's try to see if we can make it return the type of the algebra.
-/
def my_iota_type (A : MyAlgebra) (i : Nat) : MyAlgebra :=
  A

-- This should fail if my_iota_type returns MyAlgebra but we want A.carrier
-- theorem test_error_type (A : MyAlgebra) (i : Nat) :
--   use_carrier A (my_iota_type A i) = A.carrier := by
--   sorry
