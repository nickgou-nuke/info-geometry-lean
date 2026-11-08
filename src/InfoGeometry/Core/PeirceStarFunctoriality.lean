/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceCoupledCorners

/-!
# Peirce reflection and star-preserving transport

All operations use the existing Peirce corners in the original associative
ring. The reflected star reverses products. Its forward-corner readout gives
an algebraic Gram identity, without asserting positivity for an arbitrary
star ring or identifying the involution with an analytic reflection.
-/

namespace InfoGeometry.Core.PeirceStarFunctoriality

attribute [local instance 100] LieRing.ofAssociativeRing

open PeirceDecomposition PeirceGrading PeirceCoupledCorners

section Ring

variable {A B : Type*} [Ring A] [Ring B]

theorem map_reflection (f : A →+* B) (p : A) :
    f (reflection p) = reflection (f p) := by
  simp only [reflection, two_mul, map_sub, map_add, map_one]

theorem map_component10 (f : A →+* B) (p a : A) :
    f (component10 p a) = component10 (f p) (f a) := by
  simp [component10, complementIdempotent]

theorem map_component01 (f : A →+* B) (p a : A) :
    f (component01 p a) = component01 (f p) (f a) := by
  simp [component01, complementIdempotent]

/-- Every finite iterate of the native inner derivation is natural. -/
theorem map_ad_pow (f : A →+* B) (a x : A) (k : ℕ) :
    f (((LieAlgebra.ad ℤ A a) ^ k) x) =
      ((LieAlgebra.ad ℤ B (f a)) ^ k) (f x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply,
        Ring.lie_def, map_sub, map_mul, ih]

/-- The whole negative squared derivation is intertwined, on every input. -/
theorem map_neg_ad_sq (f : A →+* B) (a x : A) :
    f ((-((LieAlgebra.ad ℤ A a) ^ 2)) x) =
      (-((LieAlgebra.ad ℤ B (f a)) ^ 2)) (f x) := by
  simp only [LinearMap.neg_apply, map_neg, map_ad_pow]

theorem difference_conjugation {p : A} (hp : IsIdempotentElem p) (a b : A) :
    reflection p * (component10 p a - component01 p b) * reflection p =
      -(component10 p a - component01 p b) := by
  have h := coupled_conjugation hp (component10_mem p a) (component01_mem p (-b))
  simpa only [component01, mul_neg, neg_mul, sub_eq_add_neg] using h

end Ring

section Star

variable {A B : Type*} [Ring A] [StarRing A] [Ring B] [StarRing B]

/-- The involution reverses the multiplication order, including after reflection. -/
theorem reflected_star_mul {p : A} (hp : IsIdempotentElem p) (x y : A) :
    reflection p * star (x * y) * reflection p =
      (reflection p * star y * reflection p) *
        (reflection p * star x * reflection p) := by
  rw [star_mul]
  symm
  calc
    _ = reflection p * star y * (reflection p * reflection p) * star x *
        reflection p := by noncomm_ring
    _ = _ := by rw [reflection_sq hp]; simp only [mul_one, mul_assoc]

theorem reflected_star_involutive {p : A} (hp : IsStarProjection p) (x : A) :
    reflection p * star (reflection p * star x * reflection p) * reflection p = x := by
  simp only [star_mul, star_star, (reflection_star hp.isSelfAdjoint).star_eq]
  calc
    _ = (reflection p * reflection p) * x * (reflection p * reflection p) := by
      noncomm_ring
    _ = x := by rw [reflection_sq hp.isIdempotentElem]; simp

/-- No self-adjointness of the coefficient `a` is needed. -/
theorem reflected_star_component10 {p : A} (hp : IsStarProjection p) (a : A) :
    reflection p * star (component10 p a) * reflection p =
      -star (component10 p a) := by
  have hz : (0 : A) ∈ peirce10 p := ⟨0, by simp⟩
  have hs := star_mem_peirce01 hp.isSelfAdjoint (component10_mem p a)
  simpa only [zero_add] using coupled_conjugation hp.isIdempotentElem hz hs

/-- The exact signed reflection pairing is a Gram sum in the original ring. -/
theorem negative_reflection_pairing {p : A} (hp : IsStarProjection p) (a : A) :
    -((reflection p * star (component10 p a) * reflection p) * component10 p a +
        component10 p a * (reflection p * star (component10 p a) * reflection p)) =
      component10 p a * star (component10 p a) +
        star (component10 p a) * component10 p a := by
  rw [reflected_star_component10 hp]
  simp only [neg_mul, mul_neg, neg_add_rev, neg_neg]

/-- Adjunction of opposite corners is the hypothesis behind the Gram expression. -/
theorem opposite_corner_gram {p : A} (hp : IsSelfAdjoint p) (a : A) :
    component10 p a * component01 p (star a) +
        component01 p (star a) * component10 p a =
      component10 p a * star (component10 p a) +
        star (component10 p a) * component10 p a := by
  rw [star_component10 hp]

theorem map_reflected_star (f : A →+* B)
    (hf : ∀ x, f (star x) = star (f x)) (p x : A) :
    f (reflection p * star x * reflection p) =
      reflection (f p) * star (f x) * reflection (f p) := by
  simp only [map_mul, map_reflection, hf]

theorem map_gram (f : A →+* B)
    (hf : ∀ x, f (star x) = star (f x)) (x : A) :
    f (x * star x + star x * x) = f x * star (f x) + star (f x) * f x := by
  simp only [map_add, map_mul, hf]

/-- The mixed multiplication order is preserved by every star-preserving map. -/
theorem map_reflection_pairing (f : A →+* B)
    (hf : ∀ x, f (star x) = star (f x)) (p x : A) :
    f (-((reflection p * star x * reflection p) * x +
        x * (reflection p * star x * reflection p))) =
      -((reflection (f p) * star (f x) * reflection (f p)) * f x +
        f x * (reflection (f p) * star (f x) * reflection (f p))) := by
  simp only [map_neg, map_add, map_mul, map_reflection, hf]

end Star

end InfoGeometry.Core.PeirceStarFunctoriality
