/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Algebra.TwelveFoldPrimitiveRootArithmetic

open InfoGeometry.Algebra.FiniteSpin

/-- Non-commutativity witness for the finite spin algebra carrier. -/
theorem exists_noncomm_pair :
    ∃ x y : Mat2C, x * y ≠ y * x :=
  ⟨J_plus, J_minus, j_plus_j_minus_ne⟩

/-! Pure arithmetic for a primitive twelfth root over any domain `[Ring B] [NoZeroDivisors B]`,
with specialization to `IsPrimitiveRoot ζ 12` over `[CommRing K] [NoZeroDivisors K]`.
No Galois, braid, or physical interpretation is used in this owner. -/

/-- Over any non-commutative domain `[Ring B] [NoZeroDivisors B]`, if `ζ ^ 12 = 1`
and `ζ ^ 6 ≠ 1`, then `ζ ^ 6 = -1`. -/
theorem pow_six_eq_neg_of_pow_twelve_eq_one
    {B : Type*} [Ring B] [NoZeroDivisors B] (ζ : B)
    (h12 : ζ ^ 12 = 1) (h6_ne : ζ ^ 6 ≠ 1) :
    ζ ^ 6 = -1 := by
  have hprod : (ζ ^ 6 - 1) * (ζ ^ 6 + 1) = 0 := by
    calc
      (ζ ^ 6 - 1) * (ζ ^ 6 + 1) = ζ ^ 12 - 1 := by noncomm_ring
      _ = 0 := by rw [h12, sub_self]
  rcases mul_eq_zero.mp hprod with hminus | hplus
  · exact (h6_ne (sub_eq_zero.mp hminus)).elim
  · exact eq_neg_of_add_eq_zero_left hplus

/-- Over any non-commutative domain `[Ring B] [NoZeroDivisors B]`, if `ζ ^ 12 = 1`
and `ζ ^ 6 ≠ 1`, then `ζ ^ 7 = -ζ`. -/
theorem pow_seven_eq_neg_of_pow_twelve_eq_one
    {B : Type*} [Ring B] [NoZeroDivisors B] (ζ : B)
    (h12 : ζ ^ 12 = 1) (h6_ne : ζ ^ 6 ≠ 1) :
    ζ ^ 7 = -ζ := by
  rw [show ζ ^ 7 = ζ ^ 6 * ζ from pow_succ ζ 6,
    pow_six_eq_neg_of_pow_twelve_eq_one ζ h12 h6_ne, neg_one_mul]

/-- Over any non-commutative domain `[Ring B] [NoZeroDivisors B]`, if `ζ ^ 12 = 1`
and `ζ ^ 6 ≠ 1`, then `(ζ ^ 3) ^ 2 = -1`. -/
theorem pow_three_sq_eq_neg_of_pow_twelve_eq_one
    {B : Type*} [Ring B] [NoZeroDivisors B] (ζ : B)
    (h12 : ζ ^ 12 = 1) (h6_ne : ζ ^ 6 ≠ 1) :
    (ζ ^ 3) ^ 2 = -1 := by
  rw [show (ζ ^ 3) ^ 2 = ζ ^ 6 by rw [← pow_mul],
    pow_six_eq_neg_of_pow_twelve_eq_one ζ h12 h6_ne]

theorem primitive_root_pow_six_eq_neg
    {K : Type*} [CommRing K] [NoZeroDivisors K] (ζ : K) (hζ : IsPrimitiveRoot ζ 12) :
    ζ ^ 6 = -1 := by
  refine pow_six_eq_neg_of_pow_twelve_eq_one ζ hζ.pow_eq_one ?_
  intro h6
  have hdiv : 12 ∣ 6 := (hζ.pow_eq_one_iff_dvd 6).mp h6
  omega

theorem primitive_root_pow_seven_eq_neg
    {K : Type*} [CommRing K] [NoZeroDivisors K] (ζ : K) (hζ : IsPrimitiveRoot ζ 12) :
    ζ ^ 7 = -ζ := by
  rw [show ζ ^ 7 = ζ ^ 6 * ζ from pow_succ ζ 6,
    primitive_root_pow_six_eq_neg ζ hζ, neg_one_mul]

theorem primitive_root_pow_three_sq_eq_neg
    {K : Type*} [CommRing K] [NoZeroDivisors K] (ζ : K) (hζ : IsPrimitiveRoot ζ 12) :
    (ζ ^ 3) ^ 2 = -1 := by
  rw [show (ζ ^ 3) ^ 2 = ζ ^ 6 by rw [← pow_mul],
    primitive_root_pow_six_eq_neg ζ hζ]

end InfoGeometry.Algebra.TwelveFoldPrimitiveRootArithmetic
