/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Invertible
import Mathlib.Tactic.NoncommRing

/-!
# Quaternion factors in an associative ring

Two anticommuting square roots of `-1` determine the ordered quaternion
multiplication table. The factors `1 ± i` multiply to `2`. An inverse is
constructed only when `2` is invertible. No real Lie classification, star
operation, or membership in a Clifford Spin group is asserted.
-/

namespace InfoGeometry.Algebra.QuaternionCayley

variable {A : Type*} [Ring A]

theorem product_square (i j : A) (hi : i * i = -1) (hj : j * j = -1)
    (hji : j * i = -(i * j)) : (i * j) * (i * j) = -1 := by
  calc
    _ = i * (j * i) * j := by noncomm_ring
    _ = -(i * i) * (j * j) := by rw [hji]; noncomm_ring
    _ = -1 := by rw [hi, hj]; simp

theorem second_mul_product (i j : A) (hj : j * j = -1)
    (hji : j * i = -(i * j)) : j * (i * j) = i := by
  calc
    _ = (j * i) * j := (mul_assoc _ _ _).symm
    _ = -(i * (j * j)) := by rw [hji]; noncomm_ring
    _ = i := by rw [hj]; simp

theorem product_mul_first (i j : A) (hi : i * i = -1)
    (hji : j * i = -(i * j)) : (i * j) * i = j := by
  calc
    _ = i * (j * i) := mul_assoc _ _ _
    _ = -(i * i) * j := by rw [hji]; noncomm_ring
    _ = j := by rw [hi]; simp

theorem first_mul_product (i j : A) (hi : i * i = -1) :
    i * (i * j) = -j := by rw [← mul_assoc, hi]; simp

theorem product_mul_second (i j : A) (hj : j * j = -1) :
    (i * j) * j = -i := by rw [mul_assoc, hj]; simp

theorem factors_mul (i : A) (hi : i * i = -1) :
    (1 + i) * (1 - i) = 2 := by
  calc
    _ = 1 - i * i := by noncomm_ring
    _ = 2 := by rw [hi, sub_neg_eq_add, one_add_one_eq_two]

theorem factors_mul_reverse (i : A) (hi : i * i = -1) :
    (1 - i) * (1 + i) = 2 := by
  calc
    _ = 1 - i * i := by noncomm_ring
    _ = 2 := by rw [hi, sub_neg_eq_add, one_add_one_eq_two]

theorem factor_commutator (i j : A) (hji : j * i = -(i * j)) :
    (1 + i) * (1 + j) - (1 + j) * (1 + i) = 2 * (i * j) := by
  calc
    _ = i * j - j * i := by noncomm_ring
    _ = _ := by rw [hji]; noncomm_ring

/-- The numerator identity remains valid without dividing by `2`. -/
theorem factor_sandwich (i j : A) (hi : i * i = -1)
    (hji : j * i = -(i * j)) :
    (1 + i) * j * (1 - i) = 2 * (i * j) := by
  have htriple := product_mul_first i j hi hji
  calc
    _ = j + i * j - j * i - (i * j) * i := by noncomm_ring
    _ = _ := by rw [hji, htriple]; noncomm_ring

/-- The noncommutation claim requires excluding characteristic two. -/
theorem factors_commute_iff (i j : A) (hi : i * i = -1)
    (hj : j * j = -1) (hji : j * i = -(i * j)) :
    Commute (1 + i) (1 + j) ↔ (2 : A) = 0 := by
  change (1 + i) * (1 + j) = (1 + j) * (1 + i) ↔ _
  rw [← sub_eq_zero, factor_commutator i j hji]
  constructor
  · intro h
    have hh := congrArg (fun x : A => x * (-(i * j))) h
    simpa only [mul_assoc, mul_neg, product_square i j hi hj hji,
      neg_neg, mul_one, zero_mul, neg_zero] using hh
  · intro h
    rw [h, zero_mul]

section InvertibleTwo

variable [Invertible (2 : A)]

/-- A genuine unit with value `1 + i` and the correctly scaled inverse. -/
def factorUnit (i : A) (hi : i * i = -1) : Aˣ where
  val := 1 + i
  inv := ⅟(2 : A) * (1 - i)
  val_inv := by
    have hhalf : Commute (⅟(2 : A)) (1 + i) :=
      Commute.invOf_left ((2 : ℕ).cast_commute (1 + i))
    calc
      _ = ⅟(2 : A) * ((1 + i) * (1 - i)) := by
        rw [← mul_assoc, ← hhalf.eq, mul_assoc]
      _ = 1 := by rw [factors_mul i hi, invOf_mul_self]
  inv_val := by
    rw [mul_assoc, factors_mul_reverse i hi, invOf_mul_self]

@[simp] theorem factorUnit_val (i : A) (hi : i * i = -1) :
    (factorUnit i hi : A) = 1 + i := rfl

@[simp] theorem factorUnit_inv_val (i : A) (hi : i * i = -1) :
    (↑(factorUnit i hi)⁻¹ : A) = ⅟(2 : A) * (1 - i) := rfl

/-- Actual conjugation rotates the second quaternion axis to the product. -/
theorem factorUnit_conjugate (i j : A) (hi : i * i = -1)
    (hji : j * i = -(i * j)) :
    (factorUnit i hi : A) * j * (↑(factorUnit i hi)⁻¹ : A) = i * j := by
  have hhalf : Commute (⅟(2 : A)) ((1 + i) * j) :=
    Commute.invOf_left ((2 : ℕ).cast_commute ((1 + i) * j))
  calc
    _ = ⅟(2 : A) * ((1 + i) * j * (1 - i)) := by
      change ((1 + i) * j) * (⅟(2 : A) * (1 - i)) = _
      rw [← mul_assoc, ← hhalf.eq, mul_assoc]
    _ = i * j := by rw [factor_sandwich i j hi hji, ← mul_assoc, invOf_mul_self, one_mul]

end InvertibleTwo
end InfoGeometry.Algebra.QuaternionCayley
