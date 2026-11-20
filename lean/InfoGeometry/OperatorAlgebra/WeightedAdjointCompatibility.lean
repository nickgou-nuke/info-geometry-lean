/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Star.Basic

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

/-- Equality at an observable is equivalent to commutation with the relative
weight. The order `w * z⁻¹` is fixed by the chosen adjoint convention. -/
theorem adjoint_eq_adjoint_iff (w z : Aˣ) (x : A) :
    adjoint w x = adjoint z x ↔
      Commute (star x) ((↑w : A) * (↑z⁻¹ : A)) := by
  constructor
  · intro h
    have h' := congrArg (fun y : A => (↑w : A) * y * (↑z⁻¹ : A)) h
    change star x * ((↑w : A) * (↑z⁻¹ : A)) =
      ((↑w : A) * (↑z⁻¹ : A)) * star x
    simpa [adjoint, mul_assoc] using h'
  · intro h
    have h' := congrArg (fun y : A => (↑w⁻¹ : A) * y * (↑z : A)) h.eq
    simpa [adjoint, mul_assoc] using h'

/-- Two weighted adjoint maps agree exactly when their relative weight
commutes with every element. No commutativity of the ambient ring is assumed. -/
theorem adjoint_eq_iff_relative_central (w z : Aˣ) :
    adjoint w = adjoint z ↔
      ∀ x : A, Commute x ((↑w : A) * (↑z⁻¹ : A)) := by
  constructor
  · intro h x
    have hx := (adjoint_eq_adjoint_iff w z (star x)).mp (congrFun h (star x))
    simpa only [star_star] using hx
  · intro h
    funext x
    exact (adjoint_eq_adjoint_iff w z x).mpr (h (star x))

end InfoGeometry.OperatorAlgebra.WeightedAdjointCompatibility
