/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.NoncommutativeCayleyPair
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Exact form defects of Cayley transforms and ordered products

The ambient ring can be noncommutative. We reuse the existing explicit
right-resolvent Cayley expression, rather than defining another transform.
The equality `star U * J * U = J` is the existing Krein `IsIsometry`
predicate unfolded. No positivity, nondegeneracy, or norm bound is inferred.

Only a right inverse of `1 + x` is needed for this form identity. A two-sided
unit, or a nondegenerate self-adjoint metric, requires separate hypotheses.
The defect formula retains the order of every factor and explains precisely
how errors of different layers are transported.
-/

namespace InfoGeometry.Krein.CayleyFormTransport

open InfoGeometry.OperatorAlgebra.NoncommutativeCayleyPair
open scoped BigOperators

variable {A : Type*} [Ring A] [StarRing A]

/-- The discrepancy in an ordered product is a transported first defect
plus the second defect. The adjoint reverses the factor order. -/
theorem form_defect_mul (J U V : A) :
    star (U * V) * J * (U * V) - J =
      star V * (star U * J * U - J) * V + (star V * J * V - J) := by
  rw [star_mul]
  noncomm_ring

/-- The two polynomial factors of a Cayley transform have equal pulled-back
forms exactly up to twice the infinitesimal form defect. -/
theorem cayley_factor_form_difference (J x : A) :
    star (1 - x) * J * (1 - x) - star (1 + x) * J * (1 + x) =
      -(2 • (star x * J + J * x)) := by
  simp only [star_sub, star_add, star_one, two_nsmul]
  noncomm_ring

/-- A right resolvent pulls the denominator form back to `J`. -/
theorem resolvent_denominator_form {x r : A} (J : A)
    (hr : (1 + x) * r = 1) :
    star r * (star (1 + x) * J * (1 + x)) * r = J := by
  calc
    _ = star ((1 + x) * r) * J * ((1 + x) * r) := by
      rw [star_mul]
      noncomm_ring
    _ = J := by rw [hr, star_one, one_mul, mul_one]

/-- Exact Cayley form defect, with the actual denominator equation exposed.
This does not assume the conclusion through an isometry witness. -/
theorem cayley_form_defect {x r : A} (J : A) (hr : (1 + x) * r = 1) :
    star (cayley x r) * J * cayley x r - J =
      -(2 • (star r * (star x * J + J * x) * r)) := by
  calc
    _ = star r *
        (star (1 - x) * J * (1 - x) - star (1 + x) * J * (1 + x)) * r := by
      rw [mul_sub, sub_mul, resolvent_denominator_form J hr]
      rw [cayley, star_mul]
      noncomm_ring
    _ = _ := by
      rw [cayley_factor_form_difference]
      simp only [two_nsmul]
      noncomm_ring

/-- Infinitesimal `J`-skewness yields exact form preservation on the
explicit-resolvent domain. `J` need not be involutive for this identity. -/
theorem cayley_preserves_form {J x r : A} (hr : (1 + x) * r = 1)
    (hx : star x * J + J * x = 0) :
    star (cayley x r) * J * cayley x r = J := by
  apply sub_eq_zero.mp
  rw [cayley_form_defect J hr, hx, mul_zero, zero_mul, nsmul_zero, neg_zero]

/-- A fixed layer's finite-depth form defect is the sum of conjugated
single-layer defects. No cancellation estimate or positive norm is assumed. -/
theorem form_defect_pow (J U : A) (n : ℕ) :
    star (U ^ n) * J * U ^ n - J =
      ∑ k ∈ Finset.range n, star (U ^ k) * (star U * J * U - J) * U ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', form_defect_mul, ih, Finset.sum_range_succ]
      rw [add_comm]

/-- An ordered list of possibly different form-preserving operators
preserves the same form. No pairwise commutativity is required. -/
theorem list_prod_preserves_form (J : A) (Us : List A)
    (hUs : ∀ U ∈ Us, star U * J * U = J) :
    star Us.prod * J * Us.prod = J := by
  induction Us with
  | nil => simp
  | cons U Us ih =>
      have hU := hUs U (by simp)
      have htail := ih (fun V hV => hUs V (by simp [hV]))
      apply sub_eq_zero.mp
      rw [List.prod_cons, form_defect_mul, hU, htail]
      simp

/-- Form conservation persists through every finite power. This equation
does not imply bounded positive norm as the power increases. -/
theorem cayley_pow_preserves_form {J x r : A} (hr : (1 + x) * r = 1)
    (hx : star x * J + J * x = 0) (n : ℕ) :
    star (cayley x r ^ n) * J * cayley x r ^ n = J := by
  apply sub_eq_zero.mp
  rw [form_defect_pow, cayley_preserves_form hr hx, sub_self]
  simp

end InfoGeometry.Krein.CayleyFormTransport
