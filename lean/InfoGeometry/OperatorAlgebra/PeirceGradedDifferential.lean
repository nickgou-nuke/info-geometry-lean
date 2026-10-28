/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeircePairGeometry

/-!
# Reflection-graded differentials on the full matrix algebra

The existing reflection automorphism supplies actual parity. The expression
`U * X - σ X * U` is a twisted derivation; it squares to the inner action of
`U * U` when `U` is odd. Both directed Peirce corners therefore give genuine
square-zero actions on every matrix. Ordinary Lie or Jordan action alone does
not have this property. All operations below retain their native carriers.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceGradedDifferential

open Matrix InfoGeometry.Core.PeirceDecomposition InfoGeometry.Core.IdempotentCartan
open PeircePairGeometry

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {p : Matrix n n ℂ}

theorem reflection_conj_component10 (hp : IsIdempotentElem p) (A : Matrix n n ℂ) :
    reflectionConj p hp.eq (component10 p A) = -component10 p A := by
  change reflection p * component10 p A * reflection p = -component10 p A
  simpa only [component01, mul_zero, zero_mul, add_zero] using reflection_pair hp A 0

theorem reflection_conj_component01 (hp : IsIdempotentElem p) (A : Matrix n n ℂ) :
    reflectionConj p hp.eq (component01 p A) = -component01 p A := by
  change reflection p * component01 p A * reflection p = -component01 p A
  simpa only [component10, mul_zero, zero_mul, zero_add] using reflection_pair hp 0 A

/-- Twisted Leibniz needs multiplicativity of the automorphism, not oddness. -/
theorem twisted_leibniz (hp : IsIdempotentElem p) (U X Y : Matrix n n ℂ) :
    U * (X * Y) - reflectionConj p hp.eq (X * Y) * U =
      (U * X - reflectionConj p hp.eq X * U) * Y +
        reflectionConj p hp.eq X * (U * Y - reflectionConj p hp.eq Y * U) := by
  rw [map_mul]
  noncomm_ring

/-- An odd generator reverses the actual reflection parity. -/
theorem twisted_parity (hp : IsIdempotentElem p) {U : Matrix n n ℂ}
    (hU : reflectionConj p hp.eq U = -U) (X : Matrix n n ℂ) :
    reflectionConj p hp.eq (U * X - reflectionConj p hp.eq X * U) =
      -(U * reflectionConj p hp.eq X - X * U) := by
  have hσ : reflectionConj p hp.eq (reflectionConj p hp.eq X) = X :=
    (reflectionConj p hp.eq).left_inv X
  rw [map_sub, map_mul, map_mul, hU, hσ]
  noncomm_ring

/-- The curvature is the native inner action of the square of the generator. -/
theorem twisted_square (hp : IsIdempotentElem p) {U : Matrix n n ℂ}
    (hU : reflectionConj p hp.eq U = -U) (X : Matrix n n ℂ) :
    U * (U * X - reflectionConj p hp.eq X * U) -
      reflectionConj p hp.eq (U * X - reflectionConj p hp.eq X * U) * U =
        ⁅U * U, X⁆ := by
  rw [twisted_parity hp hU X]
  simp only [Ring.lie_def]
  noncomm_ring

theorem twisted_square_zero (hp : IsIdempotentElem p) {U : Matrix n n ℂ}
    (hU : reflectionConj p hp.eq U = -U) (hUU : U * U = 0)
    (X : Matrix n n ℂ) :
    U * (U * X - reflectionConj p hp.eq X * U) -
      reflectionConj p hp.eq (U * X - reflectionConj p hp.eq X * U) * U = 0 := by
  rw [twisted_square hp hU, hUU, zero_lie]

theorem forward_twisted_square_zero (hp : IsIdempotentElem p) (A X : Matrix n n ℂ) :
    component10 p A * (component10 p A * X - reflectionConj p hp.eq X * component10 p A) -
      reflectionConj p hp.eq
        (component10 p A * X - reflectionConj p hp.eq X * component10 p A) *
          component10 p A = 0 :=
  twisted_square_zero hp (reflection_conj_component10 hp A)
    (corners_square_zero hp.eq A).1 X

theorem reverse_twisted_square_zero (hp : IsIdempotentElem p) (A X : Matrix n n ℂ) :
    component01 p A * (component01 p A * X - reflectionConj p hp.eq X * component01 p A) -
      reflectionConj p hp.eq
        (component01 p A * X - reflectionConj p hp.eq X * component01 p A) *
          component01 p A = 0 :=
  twisted_square_zero hp (reflection_conj_component01 hp A)
    (corners_square_zero hp.eq A).2 X

/-- The even branch is ordinary Lie action, with a proved parity hypothesis. -/
theorem twisted_on_even (hp : IsIdempotentElem p) (U X : Matrix n n ℂ)
    (hX : evenPart p X = X) :
    U * X - reflectionConj p hp.eq X * U = ⁅U, X⁆ := by
  have hσ : reflectionConj p hp.eq X = X := by
    change reflection p * X * reflection p = X
    simpa only [hX] using (conjugation_on_parts hp.eq X).1
  rw [hσ, Ring.lie_def]

/-- The odd branch is the unnormalized Jordan action. -/
theorem twisted_on_odd (hp : IsIdempotentElem p) (U X : Matrix n n ℂ)
    (hX : oddPart p X = X) :
    U * X - reflectionConj p hp.eq X * U = U * X + X * U := by
  have hσ : reflectionConj p hp.eq X = -X := by
    change reflection p * X * reflection p = -X
    simpa only [hX] using (conjugation_on_parts hp.eq X).2
  rw [hσ, neg_mul, sub_neg_eq_add]

/-- Two odd twisted actions have a generally nonzero inner anticommutator. -/
theorem twisted_pair_anticommutator (hp : IsIdempotentElem p)
    {U V : Matrix n n ℂ} (hU : reflectionConj p hp.eq U = -U)
    (hV : reflectionConj p hp.eq V = -V) (X : Matrix n n ℂ) :
    (U * (V * X - reflectionConj p hp.eq X * V) -
      reflectionConj p hp.eq (V * X - reflectionConj p hp.eq X * V) * U) +
    (V * (U * X - reflectionConj p hp.eq X * U) -
      reflectionConj p hp.eq (U * X - reflectionConj p hp.eq X * U) * V) =
        ⁅U * V + V * U, X⁆ := by
  rw [twisted_parity hp hV, twisted_parity hp hU]
  simp only [Ring.lie_def]
  noncomm_ring

/-- The plus-sign companion has the same square curvature. -/
theorem twisted_plus_square (hp : IsIdempotentElem p) {U : Matrix n n ℂ}
    (hU : reflectionConj p hp.eq U = -U) (X : Matrix n n ℂ) :
    U * (U * X + reflectionConj p hp.eq X * U) +
      reflectionConj p hp.eq (U * X + reflectionConj p hp.eq X * U) * U =
        ⁅U * U, X⁆ := by
  have hσ : reflectionConj p hp.eq (reflectionConj p hp.eq X) = X :=
    (reflectionConj p hp.eq).left_inv X
  simp only [map_add, map_mul, hU, hσ, Ring.lie_def]
  noncomm_ring

/-- Opposite signs yield Jordan action instead of inner derivation. -/
theorem twisted_minus_plus_anticommutator (hp : IsIdempotentElem p)
    {U V : Matrix n n ℂ} (hU : reflectionConj p hp.eq U = -U)
    (hV : reflectionConj p hp.eq V = -V) (X : Matrix n n ℂ) :
    (U * (V * X + reflectionConj p hp.eq X * V) -
      reflectionConj p hp.eq (V * X + reflectionConj p hp.eq X * V) * U) +
    (V * (U * X - reflectionConj p hp.eq X * U) +
      reflectionConj p hp.eq (U * X - reflectionConj p hp.eq X * U) * V) =
        (U * V + V * U) * X + X * (U * V + V * U) := by
  have hσ : reflectionConj p hp.eq (reflectionConj p hp.eq X) = X :=
    (reflectionConj p hp.eq).left_inv X
  simp only [map_add, map_sub, map_mul, hU, hV, hσ]
  noncomm_ring

/-- Self-adjointness of the projection makes reflection compatible with the adjoint. -/
theorem reflection_conj_star (hp : IsStarProjection p) (X : Matrix n n ℂ) :
    reflectionConj p hp.isIdempotentElem.eq (star X) =
      star (reflectionConj p hp.isIdempotentElem.eq X) := by
  change reflection p * star X * reflection p = star (reflection p * X * reflection p)
  simp only [star_mul, reflection_star hp.isSelfAdjoint.star_eq, mul_assoc]

theorem star_is_odd (hp : IsStarProjection p) {U : Matrix n n ℂ}
    (hU : reflectionConj p hp.isIdempotentElem.eq U = -U) :
    reflectionConj p hp.isIdempotentElem.eq (star U) = -star U := by
  rw [reflection_conj_star hp, hU, star_neg]

end InfoGeometry.OperatorAlgebra.PeirceGradedDifferential
