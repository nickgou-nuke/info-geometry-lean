/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.QuadraticRotorUnit
import Mathlib.Algebra.Ring.Invertible
import Mathlib.Tactic.NoncommRing

/-!
# Quaternion pairs and Cayley-factor conjugation in an associative ring

Two anticommuting square roots of `-1` satisfy the quaternion multiplication
table with their ordered product. All polynomial identities hold in an
arbitrary ring, including characteristic two. They assert neither linear
independence nor a real compact Lie-algebra identification.

The existing quadratic rotor owner supplies the unnormalized sandwich law.
When `2` is invertible, `1 + i` is an actual unit with inverse
`(1 - i) * ⅟2`; its native inner automorphism rotates the two other axes.
No square root of two, star structure, or analytic exponential is required.
-/

namespace InfoGeometry.Algebra.QuaternionCayleyPair

open InfoGeometry.OperatorAlgebra

variable {B : Type*} [Ring B]

section QuaternionTable

variable {i j : B}

/-- Reversing an anticommuting pair reverses its ordered product. -/
theorem reverse_product (hanti : i * j + j * i = 0) :
    j * i = -(i * j) :=
  eq_neg_of_add_eq_zero_right hanti

/-- The third quaternion axis is the actual ordered product of the first two. -/
theorem product_square (hi : i * i = -1) (hj : j * j = -1)
    (hanti : i * j + j * i = 0) :
    (i * j) * (i * j) = -1 := by
  calc
    (i * j) * (i * j) = i * (j * i) * j := by simp only [mul_assoc]
    _ = -((i * i) * (j * j)) := by
      rw [reverse_product hanti]
      noncomm_ring
    _ = -1 := by rw [hi, hj]; simp

theorem first_mul_product (hi : i * i = -1) :
    i * (i * j) = -j := by
  rw [← mul_assoc, hi, neg_one_mul]

theorem product_mul_second (hj : j * j = -1) :
    (i * j) * j = -i := by
  rw [mul_assoc, hj, mul_neg_one]

theorem second_mul_product (hj : j * j = -1)
    (hanti : i * j + j * i = 0) :
    j * (i * j) = i := by
  calc
    j * (i * j) = (j * i) * j := by rw [mul_assoc]
    _ = -(i * (j * j)) := by rw [reverse_product hanti]; noncomm_ring
    _ = i := by rw [hj]; simp

theorem product_mul_first (hi : i * i = -1)
    (hanti : i * j + j * i = 0) :
    (i * j) * i = j := by
  calc
    (i * j) * i = i * (j * i) := by rw [mul_assoc]
    _ = -((i * i) * j) := by rw [reverse_product hanti]; noncomm_ring
    _ = j := by rw [hi]; simp

theorem first_product_anticommutator (hi : i * i = -1)
    (hanti : i * j + j * i = 0) :
    i * (i * j) + (i * j) * i = 0 := by
  rw [first_mul_product hi, product_mul_first hi hanti, neg_add_cancel]

theorem second_product_anticommutator (hj : j * j = -1)
    (hanti : i * j + j * i = 0) :
    j * (i * j) + (i * j) * j = 0 := by
  rw [second_mul_product hj hanti, product_mul_second hj, add_neg_cancel]

theorem first_second_commutator (hanti : i * j + j * i = 0) :
    i * j - j * i = 2 * (i * j) := by
  rw [reverse_product hanti]
  noncomm_ring

theorem second_product_commutator (hj : j * j = -1)
    (hanti : i * j + j * i = 0) :
    j * (i * j) - (i * j) * j = 2 * i := by
  rw [second_mul_product hj hanti, product_mul_second hj]
  noncomm_ring

theorem product_first_commutator (hi : i * i = -1)
    (hanti : i * j + j * i = 0) :
    (i * j) * i - i * (i * j) = 2 * j := by
  rw [product_mul_first hi hanti, first_mul_product hi]
  noncomm_ring

end QuaternionTable

section CayleyFactors

variable {i x : B}

/-- The factor product is `2`, before any inverse is introduced. -/
theorem cayley_factor_mul_reverse (hi : i * i = -1) :
    (1 + i) * (1 - i) = 2 := by
  simpa [QuadraticRotor.rotor, zsmul_eq_mul, sub_eq_add_neg] using
    (QuadraticRotor.mul_reverse (R := ℤ) i (-1) 1 1 (by simpa using hi))

/-- The reverse product is also `2` in a ring with possible zero divisors. -/
theorem cayley_reverse_mul_factor (hi : i * i = -1) :
    (1 - i) * (1 + i) = 2 := by
  have hneg : (-i) * (-i) = -1 := by simpa using hi
  simpa [sub_eq_add_neg] using cayley_factor_mul_reverse hneg

/-- Integer scalar specialization of the existing quadratic rotor sandwich. -/
theorem cayley_sandwich (hi : i * i = -1)
    (hanti : i * x + x * i = 0) :
    (1 + i) * x * (1 - i) = 2 * (i * x) := by
  simpa [QuadraticRotor.rotor, zsmul_eq_mul, sub_eq_add_neg] using
    (QuadraticRotor.sandwich (R := ℤ) i x (-1) 1 1 (by simpa using hi) hanti)

/-- Distinct axis factors retain the ordered quaternion commutator. -/
theorem cayley_factors_commutator {j : B}
    (hanti : i * j + j * i = 0) :
    (1 + i) * (1 + j) - (1 + j) * (1 + i) = 2 * (i * j) := by
  calc
    (1 + i) * (1 + j) - (1 + j) * (1 + i) = i * j - j * i := by
      noncomm_ring
    _ = 2 * (i * j) := first_second_commutator hanti

section InvertibleTwo

variable [Invertible (2 : B)]

/-- `1 + i` as a native unit, using the explicit two-sided inverse. -/
def cayleyFactorUnit (i : B) (hi : i * i = -1) : Bˣ where
  val := 1 + i
  inv := (1 - i) * ⅟(2 : B)
  val_inv := by
    rw [← mul_assoc, cayley_factor_mul_reverse hi, mul_invOf_self]
  inv_val := by
    have hhalf : Commute (⅟(2 : B)) (1 + i) :=
      Commute.invOf_left ((2 : ℕ).cast_commute (1 + i))
    calc
      ((1 - i) * ⅟(2 : B)) * (1 + i) =
          ((1 - i) * (1 + i)) * ⅟(2 : B) := by
        rw [mul_assoc, hhalf.eq, ← mul_assoc]
      _ = 1 := by rw [cayley_reverse_mul_factor hi, mul_invOf_self]

@[simp] theorem coe_cayleyFactorUnit (i : B) (hi : i * i = -1) :
    (cayleyFactorUnit i hi : B) = 1 + i := rfl

@[simp] theorem coe_cayleyFactorUnit_inv (i : B) (hi : i * i = -1) :
    (↑((cayleyFactorUnit i hi)⁻¹) : B) = (1 - i) * ⅟(2 : B) := rfl

/-- Actual inner conjugation, after cancelling the factor `2`. -/
theorem cayleyFactorUnit_conjugates (hi : i * i = -1)
    (hanti : i * x + x * i = 0) :
    innerConjugationRingEquiv (cayleyFactorUnit i hi) x = i * x := by
  change (1 + i) * x * ((1 - i) * ⅟(2 : B)) = i * x
  calc
    (1 + i) * x * ((1 - i) * ⅟(2 : B)) =
        (2 * (i * x)) * ⅟(2 : B) := by
      rw [← mul_assoc, cayley_sandwich hi hanti]
    _ = ((i * x) * 2) * ⅟(2 : B) := by noncomm_ring
    _ = i * x := by rw [mul_assoc, mul_invOf_self, mul_one]

/-- The same automorphism carries the third axis to the negative second axis. -/
theorem cayleyFactorUnit_conjugates_product {j : B}
    (hi : i * i = -1) (hanti : i * j + j * i = 0) :
    innerConjugationRingEquiv (cayleyFactorUnit i hi) (i * j) = -j := by
  rw [cayleyFactorUnit_conjugates hi (first_product_anticommutator hi hanti),
    first_mul_product hi]

/-- Noncommutation follows once two is a unit and the ambient ring is nontrivial. -/
theorem cayley_factors_not_commute [Nontrivial B] {j : B}
    (hi : i * i = -1) (hj : j * j = -1)
    (hanti : i * j + j * i = 0) :
    (1 + i) * (1 + j) ≠ (1 + j) * (1 + i) := by
  intro hcomm
  have hzero : (2 : B) * (i * j) = 0 := by
    rw [← cayley_factors_commutator hanti, hcomm, sub_self]
  have hproduct : i * j = 0 := by
    have h := congrArg (fun y : B => ⅟(2 : B) * y) hzero
    simpa only [← mul_assoc, invOf_mul_self, one_mul, mul_zero] using h
  have hsquare := product_square hi hj hanti
  rw [hproduct, zero_mul] at hsquare
  exact (neg_ne_zero.mpr (one_ne_zero : (1 : B) ≠ 0)) hsquare.symm

end InvertibleTwo
end CayleyFactors

end InfoGeometry.Algebra.QuaternionCayleyPair
