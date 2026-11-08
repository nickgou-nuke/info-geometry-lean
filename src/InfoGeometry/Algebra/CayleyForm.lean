/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Cayley preservation of an arbitrary starred-ring form

This is the congruence identity `star U * J * U = J`. The coefficient ring
need not commute; `J` need not be a positive form. The denominator inverse is
an explicit hypothesis. No positive-norm estimate or connected-component
claim follows from this algebraic identity.
-/

namespace InfoGeometry.Algebra.CayleyForm

variable {A : Type*} [Ring A] [StarRing A]

/-- The numerator and denominator induce the same form when the generator is skew for it. -/
theorem numerator_denominator_form (J Ω : A) (hΩ : star Ω * J + J * Ω = 0) :
    star (1 - Ω) * J * (1 - Ω) = star (1 + Ω) * J * (1 + Ω) := by
  have hs : star Ω * J = -(J * Ω) := eq_neg_of_add_eq_zero_left hΩ
  simp only [star_sub, star_add, star_one]
  noncomm_ring [hs]

/-- A right inverse suffices for the displayed preservation identity. -/
theorem cayley_preserves_form (J Ω r : A)
    (hΩ : star Ω * J + J * Ω = 0) (hr : (1 + Ω) * r = 1) :
    star ((1 - Ω) * r) * J * ((1 - Ω) * r) = J := by
  have hstar : star r * star (1 + Ω) = 1 := by
    simpa using congrArg star hr
  calc
    star ((1 - Ω) * r) * J * ((1 - Ω) * r) =
        star r * (star (1 - Ω) * J * (1 - Ω)) * r := by
      simp only [star_mul, mul_assoc]
    _ = star r * (star (1 + Ω) * J * (1 + Ω)) * r := by
      rw [numerator_denominator_form J Ω hΩ]
    _ = (star r * star (1 + Ω)) * J * ((1 + Ω) * r) := by
      simp only [mul_assoc]
    _ = J := by rw [hstar, hr, one_mul, mul_one]

/-- Form preservation is closed under ordered multiplication. -/
theorem mul_preserves_form (J U V : A)
    (hU : star U * J * U = J) (hV : star V * J * V = J) :
    star (U * V) * J * (U * V) = J := by
  calc
    star (U * V) * J * (U * V) = star V * (star U * J * U) * V := by
      simp only [star_mul, mul_assoc]
    _ = J := by rw [hU, hV]

/-- This preserves a form at every finite depth, without asserting a norm bound. -/
theorem pow_preserves_form (J U : A) (hU : star U * J * U = J) (n : ℕ) :
    star (U ^ n) * J * U ^ n = J := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      exact mul_preserves_form J (U ^ n) U ih hU

/-- Factors are used in their list order; no pairwise commutativity is assumed. -/
theorem list_prod_preserves_form (J : A) (w : List A)
    (hw : ∀ U ∈ w, star U * J * U = J) : star w.prod * J * w.prod = J := by
  induction w with
  | nil => simp
  | cons U w ih =>
      simp only [List.prod_cons]
      exact mul_preserves_form J U w.prod (hw U (by simp))
        (ih (fun V hV => hw V (by simp [hV])))

end InfoGeometry.Algebra.CayleyForm
