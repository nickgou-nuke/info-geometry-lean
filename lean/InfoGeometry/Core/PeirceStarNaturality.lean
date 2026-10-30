/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceSandwichDuality
import Mathlib.Algebra.Star.StarAlgHom

/-!
# Naturality and reflected star identities for Peirce corners

The existing corners and reflection are transported by native ring and
star-algebra homomorphisms. The reflected-star anticommutator is a sum of two
star squares in the original associative ring. No order structure is assumed.
-/

namespace InfoGeometry.Core.PeirceStarNaturality

open PeirceDecomposition PeirceGrading PeirceCoupledCorners PeirceSandwichDuality

variable {A B : Type*} [Ring A] [Ring B]

@[simp] theorem map_component10 (f : A →+* B) (p x : A) :
    f (component10 p x) = component10 (f p) (f x) := by
  simp only [component10, complementIdempotent, map_mul, map_sub, map_one]

@[simp] theorem map_component01 (f : A →+* B) (p x : A) :
    f (component01 p x) = component01 (f p) (f x) := by
  simp only [component01, complementIdempotent, map_mul, map_sub, map_one]

theorem map_mem_peirce10 (f : A →+* B) {p u : A} (hu : u ∈ peirce10 p) :
    f u ∈ peirce10 (f p) := by
  rcases hu with ⟨a, rfl⟩
  exact ⟨f a, by simp only [complementIdempotent, map_mul, map_sub, map_one]⟩

theorem map_mem_peirce01 (f : A →+* B) {p v : A} (hv : v ∈ peirce01 p) :
    f v ∈ peirce01 (f p) := by
  rcases hv with ⟨a, rfl⟩
  exact ⟨f a, by simp only [complementIdempotent, map_mul, map_sub, map_one]⟩

@[simp] theorem map_reflection (f : A →+* B) (p : A) :
    f (reflection p) = reflection (f p) := by
  simp only [reflection, map_sub, map_mul, map_ofNat, map_one]

/-- The difference has the same odd reflection parity as the sum. -/
theorem difference_conjugation {p u v : A} (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    reflection p * (u - v) * reflection p = -(u - v) := by
  simp only [mul_sub, sub_mul, reflection_mul_corner10 hp hu,
    reflection_mul_corner01 hp hv, neg_mul, corner10_mul_reflection hp hu,
    corner01_mul_reflection hp hv]
  abel

section Star

variable [StarRing A] [StarRing B]

@[simp] theorem map_reflected_star {R : Type*} [CommRing R]
    [Algebra R A] [Algebra R B] (f : A →⋆ₐ[R] B) (p x : A) :
    f (reflection p * star x * reflection p) =
      reflection (f p) * star (f x) * reflection (f p) := by
  simp only [map_mul, map_star]
  rw [show f (reflection p) = reflection (f p) from
    map_reflection f.toAlgHom.toRingHom p]

/-- Star reverses the corner, on which reflection conjugation has sign minus. -/
theorem reflected_star_corner {p u : A} (hp : IsStarProjection p)
    (hu : u ∈ peirce10 p) :
    reflection p * star u * reflection p = -star u := by
  have hv := star_mem_peirce01 hp.isSelfAdjoint hu
  rw [reflection_mul_corner01 hp.isIdempotentElem hv, neg_mul,
    corner01_mul_reflection hp.isIdempotentElem hv]

/-- A star-square sum identity, stated without an order or a positivity claim. -/
theorem reflected_star_anticommutator {p u : A} (hp : IsStarProjection p)
    (hu : u ∈ peirce10 p) :
    -((reflection p * star u * reflection p) * u +
        u * (reflection p * star u * reflection p)) =
      u * star u + star u * u := by
  rw [reflected_star_corner hp hu]
  simp only [neg_mul, mul_neg]
  abel

end Star

end InfoGeometry.Core.PeirceStarNaturality
