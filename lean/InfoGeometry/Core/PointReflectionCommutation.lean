/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.IdempotentGraphReflectionOrder
import Mathlib.Algebra.Group.Torsion

/-!
# Commutation of affine point reflections

The carrier is an arbitrary associative ring. The existing point reflection
is `p - (1 - p)`. Its commutator retains four times the original commutator;
no idempotence, self-adjointness, or cancellation is implicit. The converse
commutation law requires injectivity of multiplication by four on the
additive group. Ordered graph-reflection formulas remain in their owner.
-/

namespace InfoGeometry.Core.IdempotentGraphReflectionOrder

variable {B : Type*} [Ring B]

theorem pointReflection_commutator_general (p q : B) :
    pointReflection p * pointReflection q - pointReflection q * pointReflection p =
      (4 : ℕ) • (p * q - q * p) := by
  simp only [pointReflection, show (4 : ℕ) = 2 + 2 from rfl, add_nsmul, two_nsmul]
  noncomm_ring

theorem pointReflection_commute_iff_four_torsion (p q : B) :
    Commute (pointReflection p) (pointReflection q) ↔
      (4 : ℕ) • (p * q - q * p) = 0 := by
  change pointReflection p * pointReflection q =
    pointReflection q * pointReflection p ↔ _
  rw [← sub_eq_zero, pointReflection_commutator_general]

theorem pointReflection_commute_iff_of_four_injective
    (hfour : Function.Injective (fun x : B => (4 : ℕ) • x)) (p q : B) :
    Commute (pointReflection p) (pointReflection q) ↔ Commute p q := by
  rw [pointReflection_commute_iff_four_torsion]
  constructor
  · intro h
    exact sub_eq_zero.mp (hfour (h.trans (smul_zero (4 : ℕ)).symm))
  · intro h
    rw [h.eq, sub_self, smul_zero]

theorem pointReflection_commute_iff [IsAddTorsionFree B] (p q : B) :
    Commute (pointReflection p) (pointReflection q) ↔ Commute p q :=
  pointReflection_commute_iff_of_four_injective
    (IsAddTorsionFree.nsmul_right_injective (by decide : (4 : ℕ) ≠ 0)) p q

end InfoGeometry.Core.IdempotentGraphReflectionOrder
