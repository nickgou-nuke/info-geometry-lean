import InfoGeometry.Core.JordanPeirceDecomposition
import Mathlib.Tactic

/-!
# Associator of the special Jordan product

For an associative real algebra, the special Jordan product

`x ∘ y = (1 / 2) • (x * y + y * x)`

has associator equal to one quarter of the iterated associative commutator

`(x ∘ y) ∘ z - x ∘ (y ∘ z) = (1 / 4) • [y, [x, z]]`.

This theorem is an identity inside an associative envelope.  It is not an
intrinsic criterion characterizing arbitrary Jordan algebras as special.
-/

namespace InfoGeometry.Core.JordanAssociator

open InfoGeometry.Core.JordanPeirceDecomposition

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The associative commutator. -/
def commutator (x y : A) : A :=
  x * y - y * x

/-- The associator of the special Jordan product is exactly one quarter of
`[y,[x,z]]` in the ambient associative algebra. -/
theorem jordan_associator_eq_double_commutator (x y z : A) :
    jordanMul (jordanMul x y) z - jordanMul x (jordanMul y z) =
      (1 / 4 : ℝ) • commutator y (commutator x z) := by
  simp only [jordanMul, commutator,
    Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
    smul_add, smul_sub, smul_smul,
    mul_add, add_mul, mul_sub, sub_mul, mul_assoc]
  norm_num
  module

/-- Expanded form of the same associator identity, avoiding the helper
`commutator` notation. -/
theorem jordan_associator_eq_expanded_double_commutator (x y z : A) :
    jordanMul (jordanMul x y) z - jordanMul x (jordanMul y z) =
      (1 / 4 : ℝ) •
        (y * (x * z - z * x) - (x * z - z * x) * y) := by
  simpa [commutator] using
    jordan_associator_eq_double_commutator (x := x) (y := y) (z := z)

/-- If the two outer arguments commute in the ambient associative algebra,
then the special Jordan associator vanishes for every middle argument. -/
theorem jordan_associator_eq_zero_of_commute
    (x y z : A) (h : x * z = z * x) :
    jordanMul (jordanMul x y) z = jordanMul x (jordanMul y z) := by
  have hxz : commutator x z = 0 := by
    simp [commutator, h]
  have hassoc :=
    jordan_associator_eq_double_commutator (x := x) (y := y) (z := z)
  rw [hxz] at hassoc
  simp [commutator] at hassoc
  exact sub_eq_zero.mp hassoc

end InfoGeometry.Core.JordanAssociator
