/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib

/-!
# Compatibility of an adjoint with an invertible operator weight

For an arbitrary associative star ring and a unit `w`, the weighted adjoint
is `w⁻¹ * star x * w`. Agreement with the ordinary adjoint is characterized
by commutation with the weight. Self-adjoint weights give an involutive
anti-multiplicative operation. No diagonalization, positivity, or manifold
connection is assumed.
-/

namespace InfoGeometry.OperatorAlgebra.WeightedAdjointCompatibility

variable {A : Type*} [Ring A] [StarRing A]

def adjoint (w : Aˣ) (x : A) : A := (↑w⁻¹ : A) * star x * ↑w

theorem mul_adjoint (w : Aˣ) (x : A) :
    (↑w : A) * adjoint w x = star x * ↑w := by
  simp [adjoint, ← mul_assoc]

/-- The exact commutator measuring failure of agreement of the two adjoints. -/
theorem compatibility_defect (w : Aˣ) (x : A) :
    (↑w : A) * (adjoint w x - star x) =
      star x * ↑w - ↑w * star x := by
  rw [mul_sub, mul_adjoint]

theorem adjoint_eq_star_iff (w : Aˣ) (x : A) :
    adjoint w x = star x ↔ Commute (star x) (↑w : A) := by
  constructor
  · intro h
    change star x * ↑w = ↑w * star x
    rw [← mul_adjoint, h]
  · intro h
    change star x * ↑w = ↑w * star x at h
    calc
      adjoint w x = (↑w⁻¹ : A) * (star x * ↑w) := by
        simp only [adjoint, mul_assoc]
      _ = (↑w⁻¹ : A) * (↑w * star x) := by rw [h]
      _ = star x := by simp [← mul_assoc]

theorem adjoint_eq_self_iff_of_selfAdjoint (w : Aˣ) (x : A)
    (hx : star x = x) :
    adjoint w x = x ↔ Commute x (↑w : A) := by
  simpa only [hx] using adjoint_eq_star_iff w x

theorem adjoint_mul (w : Aˣ) (x y : A) :
    adjoint w (x * y) = adjoint w y * adjoint w x := by
  simp [adjoint, star_mul, mul_assoc]

theorem adjoint_involutive (w : Aˣ) (hw : star (↑w : A) = ↑w) (x : A) :
    adjoint w (adjoint w x) = x := by
  have hinv : star (↑w⁻¹ : A) = (↑w⁻¹ : A) := by
    have h := congrArg star (w.inv_val : (↑w⁻¹ : A) * ↑w = 1)
    simp only [star_mul, star_one, hw] at h
    change (↑w : A) * star (↑w⁻¹ : A) = 1 at h
    calc
      star (↑w⁻¹ : A) = (↑w⁻¹ : A) * (↑w * star (↑w⁻¹ : A)) := by
        simp [← mul_assoc]
      _ = (↑w⁻¹ : A) := by rw [h, mul_one]
  simp [adjoint, star_mul, hw, hinv, mul_assoc]

end InfoGeometry.OperatorAlgebra.WeightedAdjointCompatibility
