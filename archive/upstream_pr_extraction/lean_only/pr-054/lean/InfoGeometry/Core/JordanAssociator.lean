import InfoGeometry.Core.JordanPeirceDecomposition
import Mathlib.Tactic

/-!
# Associator diagnostic for special Jordan algebras

For an associative real algebra `A` with special Jordan product

`x ∘ y = (1/2) • (x*y + y*x)`, the Jordan associator is exactly one quarter
of the double commutator

`(x ∘ y) ∘ z - x ∘ (y ∘ z) = (1/4) • [y,[x,z]]`.

This theorem isolates the source of nonassociativity in a special Jordan
algebra: it is induced by noncommutativity of the associative envelope.
No claim is made here for intrinsically nonassociative carriers such as split
octonions or the Albert algebra.
-/

namespace InfoGeometry.Core.JordanAssociator

open InfoGeometry.Core.JordanPeirceDecomposition

section SpecialJordanAssociator

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Additive commutator in the associative envelope. -/
def commutator (x y : A) : A :=
  x * y - y * x

/-- Associator of the special Jordan product. -/
def jordanAssociator (x y z : A) : A :=
  jordanMul (jordanMul x y) z - jordanMul x (jordanMul y z)

@[simp]
theorem commutator_self (x : A) :
    commutator x x = 0 := by
  simp [commutator]

@[simp]
theorem commutator_zero_left (x : A) :
    commutator 0 x = 0 := by
  simp [commutator]

@[simp]
theorem commutator_zero_right (x : A) :
    commutator x 0 = 0 := by
  simp [commutator]

/-- Main diagnostic identity for special Jordan algebras. -/
theorem jordan_associator_eq_double_commutator (x y z : A) :
    jordanAssociator x y z =
      (1 / 4 : ℝ) • commutator y (commutator x z) := by
  simp only [jordanAssociator, commutator, jordanMul,
    Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
    smul_add, smul_sub, smul_smul]
  norm_num
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc]
  module

/-- Expanded form of the double-commutator diagnostic. -/
theorem jordan_associator_eq_expanded_double_commutator (x y z : A) :
    jordanAssociator x y z =
      (1 / 4 : ℝ) •
        (y * (x * z - z * x) - (x * z - z * x) * y) := by
  simpa [commutator] using jordan_associator_eq_double_commutator x y z

/-- If `x` and `z` commute, the corresponding special Jordan associator
vanishes for every middle argument `y`. -/
theorem jordanAssociator_eq_zero_of_commute_outer
    {x z : A} (hxz : x * z = z * x) (y : A) :
    jordanAssociator x y z = 0 := by
  rw [jordan_associator_eq_double_commutator]
  have hxz0 : commutator x z = 0 := by
    simp [commutator, hxz]
  rw [hxz0]
  simp

/-- Every commutative associative real algebra has associative special Jordan
product. -/
theorem jordanAssociator_eq_zero_of_mul_comm
    (hmul : ∀ a b : A, a * b = b * a)
    (x y z : A) :
    jordanAssociator x y z = 0 := by
  apply jordanAssociator_eq_zero_of_commute_outer (y := y)
  exact hmul x z

/-- The raw Jordan-product statement, convenient for downstream rewriting. -/
theorem jordanMul_associator_eq_double_commutator (x y z : A) :
    jordanMul (jordanMul x y) z - jordanMul x (jordanMul y z) =
      (1 / 4 : ℝ) • commutator y (commutator x z) := by
  exact jordan_associator_eq_double_commutator x y z

end SpecialJordanAssociator

end InfoGeometry.Core.JordanAssociator
