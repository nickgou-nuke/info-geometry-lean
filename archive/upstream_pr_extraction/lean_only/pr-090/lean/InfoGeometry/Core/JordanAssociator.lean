import InfoGeometry.Core.JordanPeirceDecomposition
import Mathlib.Tactic

/-!
# Associator of the special Jordan product

For an associative real algebra, the special Jordan product

`x ∘ y = (1 / 2) • (x * y + y * x)`

has associator equal to one quarter of the iterated associative commutator.
This identity is an envelope-level result; it makes no claim about arbitrary
intrinsically nonassociative carriers.
-/

namespace InfoGeometry.Core.JordanAssociator

open InfoGeometry.Core.JordanPeirceDecomposition

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The associative commutator. -/
def commutator (x y : A) : A :=
  x * y - y * x

/-- The special-Jordan associator is one quarter of `[y,[x,z]]`. -/
theorem jordan_associator_eq_double_commutator (x y z : A) :
    jordanMul (jordanMul x y) z - jordanMul x (jordanMul y z) =
      (1 / 4 : ℝ) • commutator y (commutator x z) := by
  simp only [jordanMul, commutator,
    Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
    smul_add, smul_sub, smul_smul,
    mul_add, add_mul, mul_sub, sub_mul, mul_assoc]
  norm_num
  module

/-- Expanded form of the associator identity. -/
theorem jordan_associator_eq_expanded_double_commutator (x y z : A) :
    jordanMul (jordanMul x y) z - jordanMul x (jordanMul y z) =
      (1 / 4 : ℝ) •
        (y * (x * z - z * x) - (x * z - z * x) * y) := by
  simpa [commutator] using
    jordan_associator_eq_double_commutator (x := x) (y := y) (z := z)

/-- Commuting outer arguments make the special-Jordan associator vanish. -/
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

