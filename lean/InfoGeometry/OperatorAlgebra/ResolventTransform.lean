/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Ring.Invertible
import Mathlib.Tactic.NoncommRing

/-!
# Ordered resolvent transforms in an associative ring

The transform `eta C A = Ring.inverse (1 - A * C) * A` uses Mathlib's
inverse of units. Its identities hold on the explicitly stated unit domain.
The two resolvents are related by the native spectrum symmetry for products.

Finite differences and their quadratic remainders preserve the order of all
operator factors. The analytic derivative is owned by the separate
`InfoGeometry.Analysis.ResolventTransformDifferential` module.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ResolventTransform

variable {B : Type*} [Ring B]

/-- The resolvent transform with its right-hand coefficient fixed. -/
def eta (C A : B) : B := Ring.inverse (1 - A * C) * A

/-- Jacobson's unit-domain equivalence, obtained from Mathlib's native
noncommutative spectrum symmetry over the canonical integer algebra. -/
theorem isUnit_one_sub_mul_iff (A C : B) :
    IsUnit (1 - A * C) ↔ IsUnit (1 - C * A) := by
  simpa only [spectrum.mem_iff, Units.val_one, map_one, not_iff_not] using
    (spectrum.unit_mem_mul_comm (R := ℤ) (A := B) (a := A) (b := C)
      (r := (1 : ℤˣ)))

/-- The inverse intertwiner retains the order of the two products. -/
theorem push_pull (A C : B) (hA : IsUnit (1 - A * C)) :
    Ring.inverse (1 - A * C) * A = A * Ring.inverse (1 - C * A) := by
  have hC := (isUnit_one_sub_mul_iff A C).mp hA
  have hinter : (1 - A * C) * A = A * (1 - C * A) := by noncomm_ring
  apply (Ring.eq_mul_inverse_iff_mul_eq
    (Ring.inverse (1 - A * C) * A) A (1 - C * A) hC).2
  rw [mul_assoc, ← hinter, Ring.inverse_mul_cancel_left _ _ hA]

/-- The reverse-product inverse is reconstructed from the forward resolvent. -/
theorem inverse_one_sub_mul_reverse (A C : B) (hA : IsUnit (1 - A * C)) :
    Ring.inverse (1 - C * A) = 1 + C * Ring.inverse (1 - A * C) * A := by
  have hC := (isUnit_one_sub_mul_iff A C).mp hA
  have hmul : (1 - C * A) * (1 + C * Ring.inverse (1 - A * C) * A) = 1 := by
    calc
      (1 - C * A) * (1 + C * Ring.inverse (1 - A * C) * A) =
          1 - C * A + C * ((1 - A * C) * Ring.inverse (1 - A * C)) * A := by
        noncomm_ring
      _ = 1 := by
        rw [Ring.mul_inverse_cancel _ hA]
        simp only [mul_one, sub_add_cancel]
  have hinv := (Ring.inverse_mul_eq_iff_eq_mul
    (1 - C * A) 1 (1 + C * Ring.inverse (1 - A * C) * A) hC).2 hmul.symm
  simpa only [mul_one] using hinv

/-- The ordered resolvent difference at two points of the unit domain. -/
theorem inverse_sub_one_sub_mul (C A D : B)
    (hA : IsUnit (1 - A * C)) (hD : IsUnit (1 - D * C)) :
    Ring.inverse (1 - D * C) - Ring.inverse (1 - A * C) =
      Ring.inverse (1 - D * C) * (D - A) * C * Ring.inverse (1 - A * C) := by
  calc
    Ring.inverse (1 - D * C) - Ring.inverse (1 - A * C) =
        Ring.inverse (1 - D * C) * ((1 - A * C) - (1 - D * C)) *
          Ring.inverse (1 - A * C) :=
      Ring.inverse_sub_inverse (iff_of_true hD hA)
    _ = Ring.inverse (1 - D * C) * (D - A) * C * Ring.inverse (1 - A * C) := by
      noncomm_ring

/-- Exact finite difference with the left resolvent at the new point and
the right resolvent at the base point. -/
theorem eta_sub (C A D : B)
    (hA : IsUnit (1 - A * C)) (hD : IsUnit (1 - D * C)) :
    eta C D - eta C A =
      Ring.inverse (1 - D * C) * (D - A) * Ring.inverse (1 - C * A) := by
  unfold eta
  calc
    Ring.inverse (1 - D * C) * D - Ring.inverse (1 - A * C) * A =
        Ring.inverse (1 - D * C) * (D - A) +
          (Ring.inverse (1 - D * C) - Ring.inverse (1 - A * C)) * A := by
      noncomm_ring
    _ = Ring.inverse (1 - D * C) * (D - A) +
        (Ring.inverse (1 - D * C) * (D - A) * C * Ring.inverse (1 - A * C)) * A := by
      rw [inverse_sub_one_sub_mul C A D hA hD]
    _ = Ring.inverse (1 - D * C) * (D - A) *
        (1 + C * Ring.inverse (1 - A * C) * A) := by
      noncomm_ring
    _ = Ring.inverse (1 - D * C) * (D - A) * Ring.inverse (1 - C * A) := by
      rw [← inverse_one_sub_mul_reverse A C hA]

/-- The increment form of the exact finite-difference identity. -/
theorem eta_add_sub (C A H : B)
    (hA : IsUnit (1 - A * C)) (hAH : IsUnit (1 - (A + H) * C)) :
    eta C (A + H) - eta C A =
      Ring.inverse (1 - (A + H) * C) * H * Ring.inverse (1 - C * A) := by
  simpa only [add_sub_cancel_left] using eta_sub C A (A + H) hA hAH

/-- Subtracting the base-point linear response leaves an explicit ordered
remainder containing two occurrences of the increment. -/
theorem eta_add_sub_sub_linear (C A H : B)
    (hA : IsUnit (1 - A * C)) (hAH : IsUnit (1 - (A + H) * C)) :
    eta C (A + H) - eta C A -
        Ring.inverse (1 - A * C) * H * Ring.inverse (1 - C * A) =
      Ring.inverse (1 - (A + H) * C) * H * C * Ring.inverse (1 - A * C) *
        H * Ring.inverse (1 - C * A) := by
  rw [eta_add_sub C A H hA hAH]
  calc
    Ring.inverse (1 - (A + H) * C) * H * Ring.inverse (1 - C * A) -
        Ring.inverse (1 - A * C) * H * Ring.inverse (1 - C * A) =
      (Ring.inverse (1 - (A + H) * C) - Ring.inverse (1 - A * C)) *
        H * Ring.inverse (1 - C * A) := by
      noncomm_ring
    _ = (Ring.inverse (1 - (A + H) * C) * ((A + H) - A) * C *
        Ring.inverse (1 - A * C)) * H * Ring.inverse (1 - C * A) := by
      rw [inverse_sub_one_sub_mul C A (A + H) hA hAH]
    _ = Ring.inverse (1 - (A + H) * C) * H * C * Ring.inverse (1 - A * C) *
        H * Ring.inverse (1 - C * A) := by
      rw [add_sub_cancel_left]

end InfoGeometry.OperatorAlgebra.ResolventTransform
