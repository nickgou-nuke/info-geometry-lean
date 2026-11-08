/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.IdempotentCartan

/-!
# Algebraic Peirce reflection on noncommutative star rings

This file proves the finite algebraic reflection identities for the two
directed corners of a self-adjoint idempotent. Positivity of the resulting
Gram expression is stated separately under `StarOrderedRing`; no OS state or
continuum field theory is inferred from the algebraic involution.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceOSReflection

open InfoGeometry.Core.PeirceDecomposition

variable {A : Type*} [Ring A] [StarRing A]

/-- The star reflection of the forward Peirce corner is the negative adjoint
corner, for an arbitrary noncommutative star ring. -/
theorem starReflection_component10 {p a : A}
    (hp : p * p = p) (hstar : star p = p) :
    InfoGeometry.Core.IdempotentCartan.starReflection p (component10 p a) =
      -component01 p (star a) := by
  have hstarCorner : star (component10 p a) = component01 p (star a) := by
    simp [component10, component01, complementIdempotent, star_sub, hstar, mul_assoc]
  have hodd : InfoGeometry.Core.IdempotentCartan.oddPart p
      (component01 p (star a)) = component01 p (star a) := by
    simp only [InfoGeometry.Core.IdempotentCartan.oddPart,
      component10, component01, complementIdempotent]
    noncomm_ring [hp, InfoGeometry.Core.PeirceDecomposition.idempotent_mul_nested p hp]
  unfold InfoGeometry.Core.IdempotentCartan.starReflection
  rw [hstarCorner, ← hodd]
  exact (InfoGeometry.Core.IdempotentCartan.conjugation_on_parts hp
    (component01 p (star a))).2

/-- Reflection pairing of a Peirce corner is the positive Gram sum
`c* c + c c*`, as an exact operator identity. -/
theorem reflected_corner_gram {p a : A}
    (hp : p * p = p) (hstar : star p = p) :
    -(InfoGeometry.Core.IdempotentCartan.starReflection p (component10 p a) *
        component10 p a + component10 p a *
          InfoGeometry.Core.IdempotentCartan.starReflection p (component10 p a)) =
      star (component10 p a) * component10 p a +
        component10 p a * star (component10 p a) := by
  have hstarCorner : star (component10 p a) = component01 p (star a) := by
    simp [component10, component01, complementIdempotent, star_sub, hstar, mul_assoc]
  rw [starReflection_component10 hp hstar]
  simp only [neg_mul, mul_neg]
  rw [hstarCorner]
  abel

section Ordered

variable [PartialOrder A] [StarOrderedRing A]

/-- The reflected Peirce Gram sum is nonnegative in any star-ordered ring. -/
theorem reflected_corner_gram_nonneg {p a : A}
    (hp : p * p = p) (hstar : star p = p) :
    0 ≤ -(InfoGeometry.Core.IdempotentCartan.starReflection p (component10 p a) *
        component10 p a + component10 p a *
          InfoGeometry.Core.IdempotentCartan.starReflection p (component10 p a)) := by
  rw [reflected_corner_gram hp hstar]
  exact add_nonneg (star_mul_self_nonneg _) (by
    simpa only [star_star] using (star_mul_self_nonneg (star (component10 p a))))

end Ordered

end InfoGeometry.OperatorAlgebra.PeirceOSReflection
