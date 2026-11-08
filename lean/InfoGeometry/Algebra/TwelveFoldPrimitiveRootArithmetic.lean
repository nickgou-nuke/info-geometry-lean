/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Algebra.TwelveFoldPrimitiveRootArithmetic

/-! Pure arithmetic for a primitive twelfth root.  No Galois, braid, or
physical interpretation is used in this owner. -/

theorem primitive_root_pow_six_eq_neg
    {K : Type*} [Field K] (ζ : K) (hζ : IsPrimitiveRoot ζ 12) :
    ζ ^ 6 = -1 := by
  have h12 : ζ ^ 12 = 1 := hζ.pow_eq_one
  have h6_ne : ζ ^ 6 ≠ 1 := by
    intro h6
    have hdiv : 12 ∣ 6 := (hζ.pow_eq_one_iff_dvd 6).mp h6
    omega
  have hprod : (ζ ^ 6 - 1) * (ζ ^ 6 + 1) = 0 := by
    calc
      (ζ ^ 6 - 1) * (ζ ^ 6 + 1) = ζ ^ 12 - 1 := by ring
      _ = 0 := by rw [h12]; ring
  rcases mul_eq_zero.mp hprod with hminus | hplus
  · exact (h6_ne (sub_eq_zero.mp hminus)).elim
  · exact eq_neg_of_add_eq_zero_left hplus

theorem primitive_root_pow_seven_eq_neg
    {K : Type*} [Field K] (ζ : K) (hζ : IsPrimitiveRoot ζ 12) :
    ζ ^ 7 = -ζ := by
  rw [show ζ ^ 7 = ζ ^ 6 * ζ by ring,
    primitive_root_pow_six_eq_neg ζ hζ, neg_one_mul]

theorem primitive_root_pow_three_sq_eq_neg
    {K : Type*} [Field K] (ζ : K) (hζ : IsPrimitiveRoot ζ 12) :
    (ζ ^ 3) ^ 2 = -1 := by
  rw [show (ζ ^ 3) ^ 2 = ζ ^ 6 by ring,
    primitive_root_pow_six_eq_neg ζ hζ]

end InfoGeometry.Algebra.TwelveFoldPrimitiveRootArithmetic
