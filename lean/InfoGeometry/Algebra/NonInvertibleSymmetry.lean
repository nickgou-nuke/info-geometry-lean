/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Units.Defs

/-!
# Noninvertible operators from idempotents

This module records two elementary operator-algebra facts that can be stated
without importing unformalized claims about lattice fermions or fusion
categories: a proper idempotent has no two-sided inverse, while an element of
positive finite multiplicative order is a unit.
-/

namespace InfoGeometry.Algebra.NonInvertibleSymmetry

variable {R : Type*} [Ring R]

/-- An idempotent different from the identity. -/
def IsProperIdempotent (e : R) : Prop := e * e = e ∧ e ≠ 1

/-- A proper idempotent cannot have a two-sided multiplicative inverse. -/
theorem proper_idempotent_no_two_sided_inverse {e : R} (he : IsProperIdempotent e) :
    ¬ ∃ u : R, u * e = 1 ∧ e * u = 1 := by
  rintro ⟨u, hu_left, hu_right⟩
  apply he.2
  calc
    e = (u * e) * e := by rw [hu_left, one_mul]
    _ = u * (e * e) := by rw [mul_assoc]
    _ = u * e := by rw [he.1]
    _ = 1 := hu_left

variable {M : Type*} [Monoid M]

/-- A positive finite-order element is a unit, with inverse the preceding power. -/
theorem finite_order_element_isUnit {x : M} {n : ℕ} (hn : 0 < n)
    (hpow : x ^ n = 1) : IsUnit x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  apply (isUnit_iff_exists).2
  refine ⟨x ^ k, ?_, ?_⟩
  · simpa [pow_succ'] using hpow
  · simpa [pow_succ] using hpow

end InfoGeometry.Algebra.NonInvertibleSymmetry
