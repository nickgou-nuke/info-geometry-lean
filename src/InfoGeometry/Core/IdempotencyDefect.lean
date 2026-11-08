/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Tactic.NoncommRing

/-!
# The idempotency defect in an associative ring

Polarization of the quadratic map `x ↦ x*x-x` recovers the anticommutator.
The identities retain the order of every mixed product. No commutativity or
division by two is assumed.
-/

namespace InfoGeometry.Core.IdempotencyDefect

variable {A B : Type*} [Ring A] [Ring B]

/-- The polynomial obstruction to idempotence. -/
def defect (x : A) : A := x * x - x

@[simp] theorem defect_zero : defect (0 : A) = 0 := by
  simp [defect]

@[simp] theorem defect_eq_zero_iff (x : A) :
    defect x = 0 ↔ IsIdempotentElem x := by
  change x * x - x = 0 ↔ x * x = x
  exact sub_eq_zero

theorem map_defect (f : A →+* B) (x : A) :
    f (defect x) = defect (f x) := by
  simp only [defect, map_sub, map_mul]

/-- This is a quadratic second difference, not an oriented commutator. -/
theorem polarization (x y : A) :
    defect (x + y) - defect x - defect y = x * y + y * x := by
  unfold defect
  noncomm_ring

theorem defect_neg_add (x : A) :
    defect (-x) + defect x = 2 • (x * x) := by
  simp only [defect, two_nsmul]
  noncomm_ring

theorem defect_neg_sub (x : A) :
    defect (-x) - defect x = 2 • x := by
  simp only [defect, two_nsmul]
  noncomm_ring

theorem defect_mul_defect_neg (x : A) :
    defect x * defect (-x) = defect (x * x) := by
  unfold defect
  noncomm_ring

/-- The cubic obstruction factors through the idempotency defect. -/
theorem cubic_sub_eq_mul_defect (x : A) :
    x * x * x - x = (x + 1) * defect x := by
  unfold defect
  noncomm_ring

/-- Negating the input gives the complementary cubic factorization. -/
theorem cubic_sub_eq_mul_defect_neg (x : A) :
    x * x * x - x = (x - 1) * defect (-x) := by
  unfold defect
  noncomm_ring

/-- Mutually annihilating summands have no polarization term. -/
theorem defect_add_of_mul_eq_zero {x y : A}
    (hxy : x * y = 0) (hyx : y * x = 0) :
    defect (x + y) = defect x + defect y := by
  unfold defect
  noncomm_ring [hxy, hyx]

theorem defect_mul_eq_zero {x y : A} (hxy : x * y = 0) :
    defect x * y = 0 := by
  simp only [defect, sub_mul, mul_assoc, hxy, mul_zero, sub_self]

theorem mul_defect_eq_zero {x y : A} (hxy : x * y = 0) :
    x * defect y = 0 := by
  simp only [defect, mul_sub, ← mul_assoc, hxy, zero_mul, sub_self]

end InfoGeometry.Core.IdempotencyDefect
