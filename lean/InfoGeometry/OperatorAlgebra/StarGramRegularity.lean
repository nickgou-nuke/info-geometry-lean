/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel

/-!
# Three-square star faithfulness and Gram regularity

Faithfulness of a sum of three star squares supplies properness,
cancellation of doubling, and both-sided regularity of the Gram denominator.
The coefficient ring remains noncommutative; no order structure is assumed.
-/

namespace InfoGeometry.OperatorAlgebra

/-- A sum of three star squares vanishes only when all three terms vanish. -/
def ThreeSumStarFaithful (B : Type*) [Ring B] [StarRing B] : Prop :=
  ∀ x y z : B, star x * x + star y * y + star z * z = 0 → x = 0 ∧ y = 0 ∧ z = 0

namespace ThreeSumStarFaithful

variable {B : Type*} [Ring B] [StarRing B]

/-- Three-square faithfulness implies properness of the involution. -/
theorem proper (hF : ThreeSumStarFaithful B) {x : B}
    (hx : star x * x = 0) : x = 0 :=
  (hF x 0 0 (by simpa using hx)).1

/-- Faithfulness rules out additive two-torsion, not just characteristic two. -/
theorem doubling_injective (hF : ThreeSumStarFaithful B) :
    Function.Injective (fun x : B => (2 : ℕ) • x) := by
  intro x y hxy
  apply sub_eq_zero.mp
  have hz : (x - y) + (x - y) = 0 := by
    calc
      _ = (x + x) - (y + y) := by abel
      _ = 0 := sub_eq_zero.mpr (by simpa only [two_nsmul] using hxy)
  apply (hF (x - y) (x - y) 0 ?_).1
  simp only [star_zero, mul_zero, add_zero, ← mul_add, hz]

/-- The Gram denominator is left regular on the entire noncommutative ring. -/
theorem one_add_gram_left_injective (hF : ThreeSumStarFaithful B) (N : B) :
    Function.Injective (fun x : B => (1 + (N * star N + star N * N)) * x) := by
  intro x y hxy
  apply sub_eq_zero.mp
  let z := x - y
  have hz : (1 + (N * star N + star N * N)) * z = 0 := by
    dsimp [z]
    rw [mul_sub]
    exact sub_eq_zero.mpr hxy
  change z = 0
  apply (hF z (star N * z) (N * z) ?_).1
  calc
    _ = star z * ((1 + (N * star N + star N * N)) * z) := by
      simp only [star_mul, star_star]
      noncomm_ring
    _ = 0 := by rw [hz, mul_zero]

/-- Self-adjointness transports left regularity to right regularity. -/
theorem one_add_gram_right_injective (hF : ThreeSumStarFaithful B) (N : B) :
    Function.Injective (fun x : B => x * (1 + (N * star N + star N * N))) := by
  intro x y hxy
  apply star_injective
  apply hF.one_add_gram_left_injective N
  simpa only [star_mul, star_add, star_one, star_star] using congrArg star hxy

end ThreeSumStarFaithful
end InfoGeometry.OperatorAlgebra
