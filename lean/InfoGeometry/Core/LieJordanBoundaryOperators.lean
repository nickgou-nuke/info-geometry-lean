/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.LieJordanComposition
import Mathlib.Algebra.Module.Submodule.Range

/-!
# Exact compositions of native Lie and Jordan actions

The adjoint action, Jordan multiplication, and two-sided multiplication are
the existing native endomorphisms. The generator-swapped mixed difference
retains its sandwich correction. Square-zero coefficients annihilate the
mixed composites; the individual squares retain the exact sandwich term.
-/

namespace InfoGeometry.Core.LieJordanBoundaryOperators

attribute [local instance 100] LieRing.ofAssociativeRing

open JordanMultiplicationClosure

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

theorem ad_mul_jordan_self (a : A) :
    LieAlgebra.ad R A a * jordanLeft (R := R) a =
      LieAlgebra.ad R A (a * a) := by
  apply LinearMap.ext
  intro x
  change a * (a * x + x * a) - (a * x + x * a) * a =
    (a * a) * x - x * (a * a)
  noncomm_ring

theorem jordan_mul_ad_self (a : A) :
    jordanLeft (R := R) a * LieAlgebra.ad R A a =
      LieAlgebra.ad R A (a * a) := by
  apply LinearMap.ext
  intro x
  change a * (a * x - x * a) + (a * x - x * a) * a =
    (a * a) * x - x * (a * a)
  noncomm_ring

theorem ad_mul_jordan_add (a b : A) :
    LieAlgebra.ad R A a * jordanLeft (R := R) b +
      LieAlgebra.ad R A b * jordanLeft (R := R) a =
        LieAlgebra.ad R A (a * b + b * a) := by
  apply LinearMap.ext
  intro x
  change (a * (b * x + x * b) - (b * x + x * b) * a) +
    (b * (a * x + x * a) - (a * x + x * a) * b) =
      (a * b + b * a) * x - x * (a * b + b * a)
  noncomm_ring

theorem jordan_mul_ad_add (a b : A) :
    jordanLeft (R := R) a * LieAlgebra.ad R A b +
      jordanLeft (R := R) b * LieAlgebra.ad R A a =
        LieAlgebra.ad R A (a * b + b * a) := by
  apply LinearMap.ext
  intro x
  change (a * (b * x - x * b) + (b * x - x * b) * a) +
    (b * (a * x - x * a) + (a * x - x * a) * b) =
      (a * b + b * a) * x - x * (a * b + b * a)
  noncomm_ring

/-- Swapping the two coefficients differs from the owned operator bracket. -/
theorem ad_mul_jordan_sub (a b : A) :
    LieAlgebra.ad R A a * jordanLeft (R := R) b -
      LieAlgebra.ad R A b * jordanLeft (R := R) a =
        jordanLeft (R := R) ⁅a, b⁆ +
          2 • (LinearMap.mulLeftRight R (a, b) - LinearMap.mulLeftRight R (b, a)) := by
  rw [two_nsmul]
  apply LinearMap.ext
  intro x
  change (a * (b * x + x * b) - (b * x + x * b) * a) -
    (b * (a * x + x * a) - (a * x + x * a) * b) =
      ((a * b - b * a) * x + x * (a * b - b * a)) +
        ((a * x * b - b * x * a) + (a * x * b - b * x * a))
  noncomm_ring

theorem jordan_mul_jordan_add (a b : A) :
    jordanLeft (R := R) a * jordanLeft (R := R) b +
      jordanLeft (R := R) b * jordanLeft (R := R) a =
        jordanLeft (R := R) (a * b + b * a) +
          2 • (LinearMap.mulLeftRight R (a, b) + LinearMap.mulLeftRight R (b, a)) := by
  rw [two_nsmul]
  apply LinearMap.ext
  intro x
  change (a * (b * x + x * b) + (b * x + x * b) * a) +
    (b * (a * x + x * a) + (a * x + x * a) * b) =
      ((a * b + b * a) * x + x * (a * b + b * a)) +
        ((a * x * b + b * x * a) + (a * x * b + b * x * a))
  noncomm_ring

theorem ad_mul_ad_add (a b : A) :
    LieAlgebra.ad R A a * LieAlgebra.ad R A b +
      LieAlgebra.ad R A b * LieAlgebra.ad R A a =
        jordanLeft (R := R) (a * b + b * a) -
          2 • (LinearMap.mulLeftRight R (a, b) + LinearMap.mulLeftRight R (b, a)) := by
  rw [two_nsmul]
  apply LinearMap.ext
  intro x
  change (a * (b * x - x * b) - (b * x - x * b) * a) +
    (b * (a * x - x * a) - (a * x - x * a) * b) =
      ((a * b + b * a) * x + x * (a * b + b * a)) -
        ((a * x * b + b * x * a) + (a * x * b + b * x * a))
  noncomm_ring

theorem pure_compositions_add (a b : A) :
    (jordanLeft (R := R) a * jordanLeft (R := R) b +
      jordanLeft (R := R) b * jordanLeft (R := R) a) +
      (LieAlgebra.ad R A a * LieAlgebra.ad R A b +
        LieAlgebra.ad R A b * LieAlgebra.ad R A a) =
          2 • jordanLeft (R := R) (a * b + b * a) := by
  rw [jordan_mul_jordan_add, ad_mul_ad_add]
  simp only [two_nsmul]
  abel

theorem pure_compositions_sub (a b : A) :
    (jordanLeft (R := R) a * jordanLeft (R := R) b +
      jordanLeft (R := R) b * jordanLeft (R := R) a) -
      (LieAlgebra.ad R A a * LieAlgebra.ad R A b +
        LieAlgebra.ad R A b * LieAlgebra.ad R A a) =
          4 • (LinearMap.mulLeftRight R (a, b) + LinearMap.mulLeftRight R (b, a)) := by
  rw [jordan_mul_jordan_add, ad_mul_ad_add]
  rw [show (4 : ℕ) = 2 + 2 by decide, add_nsmul]
  simp only [two_nsmul]
  abel

/-- The individual adjoint square includes the full two-sided action. -/
theorem ad_sq (a : A) :
    LieAlgebra.ad R A a ^ 2 =
      jordanLeft (R := R) (a * a) - 2 • LinearMap.mulLeftRight R (a, a) := by
  rw [pow_two, two_nsmul]
  apply LinearMap.ext
  intro x
  change a * (a * x - x * a) - (a * x - x * a) * a =
    ((a * a) * x + x * (a * a)) - (a * x * a + a * x * a)
  noncomm_ring

theorem jordan_sq (a : A) :
    jordanLeft (R := R) a ^ 2 =
      jordanLeft (R := R) (a * a) + 2 • LinearMap.mulLeftRight R (a, a) := by
  rw [pow_two, two_nsmul]
  apply LinearMap.ext
  intro x
  change a * (a * x + x * a) + (a * x + x * a) * a =
    ((a * a) * x + x * (a * a)) + (a * x * a + a * x * a)
  noncomm_ring

section SquareZero

variable {a : A} (ha : a * a = 0)

theorem ad_mul_jordan_eq_zero :
    LieAlgebra.ad R A a * jordanLeft (R := R) a = 0 := by
  rw [ad_mul_jordan_self, ha, map_zero]

theorem jordan_mul_ad_eq_zero :
    jordanLeft (R := R) a * LieAlgebra.ad R A a = 0 := by
  rw [jordan_mul_ad_self, ha, map_zero]

theorem range_jordan_le_ker_ad :
    LinearMap.range (jordanLeft (R := R) a) ≤ LinearMap.ker (LieAlgebra.ad R A a) :=
  LinearMap.range_le_ker_iff.mpr (ad_mul_jordan_eq_zero (R := R) ha)

theorem range_ad_le_ker_jordan :
    LinearMap.range (LieAlgebra.ad R A a) ≤ LinearMap.ker (jordanLeft (R := R) a) :=
  LinearMap.range_le_ker_iff.mpr (jordan_mul_ad_eq_zero (R := R) ha)

theorem ad_sq_of_sq_zero :
    LieAlgebra.ad R A a ^ 2 = -(2 • LinearMap.mulLeftRight R (a, a)) := by
  rw [ad_sq, ha]
  apply LinearMap.ext
  intro x
  simp [jordanLeft]

theorem jordan_sq_of_sq_zero :
    jordanLeft (R := R) a ^ 2 = 2 • LinearMap.mulLeftRight R (a, a) := by
  rw [jordan_sq, ha]
  apply LinearMap.ext
  intro x
  simp [jordanLeft]

theorem ad_sq_eq_zero_iff :
    LieAlgebra.ad R A a ^ 2 = 0 ↔ 2 • LinearMap.mulLeftRight R (a, a) = 0 := by
  rw [ad_sq_of_sq_zero ha, neg_eq_zero]

theorem jordan_sq_eq_zero_iff :
    jordanLeft (R := R) a ^ 2 = 0 ↔ 2 • LinearMap.mulLeftRight R (a, a) = 0 := by
  rw [jordan_sq_of_sq_zero ha]

end SquareZero

end InfoGeometry.Core.LieJordanBoundaryOperators
