/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.IsotropicCyclotomicGalois
import Mathlib.Tactic.NoncommRing

/-! # Cubic nilpotents: cyclotomic inverses and inner-derivation tower -/

namespace InfoGeometry.Algebra.CubicNilpotentAdjoint

open InfoGeometry.Algebra.IsotropicCyclotomicGalois

variable {B : Type*} [Ring B]

lemma cube_zero_left (a x : B) (ha : a * a * a = 0) :
    a * (a * (a * x)) = 0 := by
  rw [← mul_assoc, ← mul_assoc, ha, zero_mul]

lemma cube_zero_right (a x : B) (ha : a * a * a = 0) :
    ((x * a) * a) * a = 0 := by
  calc
    ((x * a) * a) * a = x * (a * a * a) := by noncomm_ring
    _ = 0 := by rw [ha, mul_zero]

/-- Cyclotomic inverses for a cube-zero operator, without division. -/
theorem cube_zero_cyclotomic_inverses (a : B) (ha : a * a * a = 0) :
    (1 - a) * cyclo3 a = 1 ∧ cyclo3 a * (1 - a) = 1 ∧
    (1 + a) * cyclo6 a = 1 ∧ cyclo6 a * (1 + a) = 1 := by
  have hLeft : a * (a * a) = 0 := by
    calc
      a * (a * a) = a * a * a := by noncomm_ring
      _ = 0 := ha
  have hRight : (a * a) * a = 0 := ha
  dsimp [cyclo3, cyclo6]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring [ha, hLeft, hRight]

/-- The first four iterates of the inner derivation for a cube-zero generator. -/
theorem cube_zero_inner_derivation_tower (a x : B) (ha : a * a * a = 0) :
    innerDerivation a (innerDerivation a x) =
      a * a * x - (2 : ℤ) • (a * x * a) + x * a * a ∧
    innerDerivation a (innerDerivation a (innerDerivation a x)) =
      -((3 : ℤ) • (a * a * x * a - a * x * a * a)) ∧
    innerDerivation a (innerDerivation a (innerDerivation a
      (innerDerivation a x))) = (6 : ℤ) • (a * a * x * a * a) ∧
    innerDerivation a (innerDerivation a (innerDerivation a
      (innerDerivation a (innerDerivation a x)))) = 0 := by
  have hL : ∀ y : B, a * (a * (a * y)) = 0 := fun y => cube_zero_left a y ha
  have hR : ∀ y : B, ((y * a) * a) * a = 0 := fun y => cube_zero_right a y ha
  simp only [innerDerivation, InfoGeometry.Algebra.IsotropicCyclotomicGalois.commutator]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    noncomm_ring [ha, hL x, hR x, hL (x * a), hR (a * x),
      hL (a * x * a), hR (a * x * a), hL (x * (a * a))]

end InfoGeometry.Algebra.CubicNilpotentAdjoint
