/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
namespace InfoGeometry.SignedNetwork.RegularBimoduleSeparation
variable {A : Type*} [Ring A]
def leftAction (a : A) : A →+ A := { toFun := fun x => a*x, map_zero' := mul_zero a, map_add' := fun x y => mul_add a x y }
def rightAction (b : A) : A →+ A := { toFun := fun x => x*b, map_zero' := zero_mul b, map_add' := fun x y => add_mul x y b }
theorem left_right_commute (a b : A) : (leftAction a).comp (rightAction b) = (rightAction b).comp (leftAction a) := by
  ext x
  simp [leftAction, rightAction, mul_assoc]
theorem commutant_characterization (T : A →+ A) :
    (∀ a x, T (a*x) = a*T x) ↔ ∀ x, T x = x * T 1 := by
  constructor
  · intro h x
    simpa using h x 1
  · intro h a x
    rw [h (a*x), h x]
    simp [mul_assoc]

@[simp] theorem leftAction_apply (a x : A) : leftAction a x = a * x := rfl
@[simp] theorem rightAction_apply (b x : A) : rightAction b x = x * b := rfl

theorem rightAction_comp (a b : A) :
    (rightAction a).comp (rightAction b) = rightAction (b * a) := by
  ext x
  exact mul_assoc x b a

theorem commutes_left_iff_right (T : A → A) :
    (∀ a x, T (a * x) = a * T x) ↔ ∀ x, T x = x * T 1 := by
  constructor
  · intro h x
    simpa only [mul_one] using h x 1
  · intro h a x
    rw [h (a * x), h x, mul_assoc]

section Star

variable {A : Type*} [Ring A] [StarRing A]

/-- Algebraic conjugation on the standard regular carrier. -/
def conjugation (x : A) : A := star x

@[simp] theorem conjugation_involutive (x : A) :
    conjugation (conjugation x) = x := by simp [conjugation]

theorem conjugation_left (a x : A) :
    conjugation (leftAction a (conjugation x)) = rightAction (star a) x := by
  simp [conjugation, star_mul]

theorem conjugation_right (a x : A) :
    conjugation (rightAction a (conjugation x)) = leftAction (star a) x := by
  simp [conjugation, star_mul]

end Star

section Nonassociative

variable {Z : Type*} [AddCommGroup Z] [Mul Z]

/-- The multiplication is deliberately unbundled from any associativity law. -/
def associator (a x b : Z) : Z := (a * x) * b - a * (x * b)

theorem left_right_defect (a x b : Z) :
    a * (x * b) - (a * x) * b = -associator a x b := by
  unfold associator
  abel

theorem left_right_commute_iff (a x b : Z) :
    a * (x * b) = (a * x) * b ↔ associator a x b = 0 := by
  unfold associator
  rw [sub_eq_zero, eq_comm]

end Nonassociative
end InfoGeometry.SignedNetwork.RegularBimoduleSeparation
