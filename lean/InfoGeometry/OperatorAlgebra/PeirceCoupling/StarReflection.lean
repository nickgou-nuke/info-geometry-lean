/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceCoupling.Algebra

/-!
# Star-reflection of an actual Peirce corner

The carrier, corner maps and reflection are the existing owners. The map
`x ↦ reflection p * star x * reflection p` is an algebraic anti-involution.
Its Gram identity and the vanishing alternative pairing are distinct facts.
No Osterwalder--Schrader state or spacetime reflection is constructed here.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceCoupling

open InfoGeometry.Core.PeirceDecomposition InfoGeometry.Core.PeirceGrading

variable {A : Type*} [Ring A] [StarRing A] {p : A}

/-- Reflection reverses multiplication order. -/
theorem starReflection_mul (hp : IsIdempotentElem p) (x y : A) :
    reflection p * star (x * y) * reflection p =
      (reflection p * star y * reflection p) *
        (reflection p * star x * reflection p) := by
  rw [star_mul]
  symm
  calc
    _ = reflection p * star y * (reflection p * reflection p) *
        star x * reflection p := by noncomm_ring
    _ = _ := by rw [reflection_sq hp]; simp only [mul_one, mul_assoc]

/-- Star self-adjointness is used, not inferred from idempotence. -/
theorem starReflection_involutive (hp : IsStarProjection p) (x : A) :
    reflection p * star (reflection p * star x * reflection p) * reflection p = x := by
  have hs := (reflection_star hp.isSelfAdjoint).star_eq
  simp only [star_mul, hs, star_star]
  calc
    _ = (reflection p * reflection p) * x * (reflection p * reflection p) := by
      simp only [mul_assoc]
    _ = x := by rw [reflection_sq hp.isIdempotentElem]; simp

/-- The star of the forward corner is the reversed corner of the star. -/
theorem star_component10 (hp : IsSelfAdjoint p) (a : A) :
    star (component10 p a) = component01 p (star a) := by
  simp only [component10, component01, complementIdempotent, star_mul,
    star_sub, star_one, hp.star_eq, mul_assoc]

/-- The reflected forward corner is minus its actual adjoint. -/
theorem starReflection_component10 (hp : IsStarProjection p) (a : A) :
    reflection p * star (component10 p a) * reflection p = -star (component10 p a) := by
  rw [star_component10 hp.isSelfAdjoint]
  have hl : p * component01 p (star a) = 0 := by
    change p * ((1 - p) * star a * p) = 0
    calc
      _ = (p * (1 - p)) * (star a * p) := by simp only [mul_assoc]
      _ = 0 := by rw [hp.isIdempotentElem.mul_one_sub_self, zero_mul]
  have hr : component01 p (star a) * p = component01 p (star a) := by
    change ((1 - p) * star a * p) * p = (1 - p) * star a * p
    rw [mul_assoc, hp.isIdempotentElem.eq]
  have hsl : reflection p * component01 p (star a) = -component01 p (star a) := by
    simp only [reflection, two_mul, sub_mul, add_mul, hl, one_mul]
    abel
  have hsr : component01 p (star a) * reflection p = component01 p (star a) := by
    simp only [reflection, two_mul, mul_sub, mul_add, hr, mul_one]
    abel
  rw [hsl, neg_mul, hsr]

/-- The negative reflected anticommutator is exactly the two-sided Gram sum. -/
theorem starReflection_gram_identity (hp : IsStarProjection p) (a : A) :
    -((reflection p * star (component10 p a) * reflection p) * component10 p a +
      component10 p a * (reflection p * star (component10 p a) * reflection p)) =
      component10 p a * star (component10 p a) +
        star (component10 p a) * component10 p a := by
  rw [starReflection_component10 hp a]
  noncomm_ring

theorem starReflection_lie_identity (hp : IsStarProjection p) (a : A) :
    ⁅reflection p * star (component10 p a) * reflection p, component10 p a⁆ =
      ⁅component10 p a, star (component10 p a)⁆ := by
  rw [starReflection_component10 hp a]
  change (-star (component10 p a)) * component10 p a -
    component10 p a * (-star (component10 p a)) = _
  change _ = component10 p a * star (component10 p a) -
    star (component10 p a) * component10 p a
  noncomm_ring

/-- The pairing printed in the intake is zero, not the Gram sum. -/
theorem starReflection_star_pairing_zero (hp : IsStarProjection p) (a : A) :
    star (reflection p * star (component10 p a) * reflection p) * component10 p a = 0 := by
  have hn : component10 p a * component10 p a = 0 := by
    simpa only [component10, complementIdempotent, pow_two] using
      (corners_sq_zero hp.isIdempotentElem a).1
  rw [starReflection_component10 hp a, star_neg, star_star, neg_mul, hn, neg_zero]

omit [StarRing A] in
/-- The positive and negative weights are native commutator identities. -/
theorem reflection_corner_weights (hp : IsIdempotentElem p) (a b : A) :
    ⁅reflection p, component10 p a⁆ = (2 : ℕ) • component10 p a ∧
    ⁅reflection p, component01 p b⁆ = -((2 : ℕ) • component01 p b) := by
  have hpu : p * component10 p a = component10 p a := peirceCorner_absorb_left hp.eq
  have hup : component10 p a * p = 0 := by
    change (p * a * complementIdempotent p) * p = 0
    rw [mul_assoc, complement_mul_idempotent p hp.eq, mul_zero]
  have hpv : p * component01 p b = 0 := by
    change p * (complementIdempotent p * b * p) = 0
    calc
      _ = (p * complementIdempotent p) * (b * p) := by simp only [mul_assoc]
      _ = 0 := by rw [idempotent_mul_complement p hp.eq, zero_mul]
  have hvp : component01 p b * p = component01 p b := peirceCorner_absorb_right hp.eq
  constructor
  · change reflection p * component10 p a - component10 p a * reflection p = _
    rw [reflection_commutator, hpu, hup, sub_zero]
  · change reflection p * component01 p b - component01 p b * reflection p = _
    rw [reflection_commutator, hpv, hvp, zero_sub, smul_neg]

end InfoGeometry.OperatorAlgebra.PeirceCoupling
