/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.DerivationGaugeTransport
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Convert

/-!
# Native right logarithmic forms on noncommutative units

The right logarithmic form is the native one-cochain `η_g(x) = ρ_x(g)g⁻¹`.
Its ordered product law and right Maurer--Cartan equation use the existing
derivation action and CE differential. The zero-connection gauge transform
is `-η_g`, which fixes the sign of the Maurer--Cartan equation.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

open InfoGeometry.Algebra
open InfoGeometry.Geometry.AssociativeGaugeConnection (conjugate)

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable (K : DerivationLieLane R A)

/-- Right multiplication by the inverse follows the represented derivative. -/
def rightLogarithmicOneForm (g : Aˣ) : OneForm K :=
  (LinearMap.mulRight R (↑g⁻¹ : A)).comp (exteriorDerivativeZero K (g : A))

@[simp] theorem rightLogarithmicOneForm_apply (g : Aˣ) (x : K.L) :
    rightLogarithmicOneForm K g x =
      K.operatorAction x (g : A) * (↑g⁻¹ : A) := rfl

/-- The right logarithmic form obeys an ordered conjugation cocycle law. -/
theorem rightLogarithmicOneForm_mul (g h : Aˣ) (x : K.L) :
    rightLogarithmicOneForm K (g * h) x =
      rightLogarithmicOneForm K g x +
        conjugate g (rightLogarithmicOneForm K h x) := by
  simp only [rightLogarithmicOneForm_apply, Units.val_mul, mul_inv_rev,
    K.operatorAction_leibniz, conjugate, add_mul, mul_assoc,
    Units.mul_inv_cancel_left]

/-- The ordered quotient uses conjugation by the entire unit `u * Δ⁻¹`. -/
theorem rightLogarithmicOneForm_mul_inv (u Δ : Aˣ) (x : K.L) :
    rightLogarithmicOneForm K (u * Δ⁻¹) x =
      rightLogarithmicOneForm K u x -
        conjugate (u * Δ⁻¹) (rightLogarithmicOneForm K Δ x) := by
  simp only [rightLogarithmicOneForm_apply, Units.val_mul, mul_inv_rev, inv_inv,
    K.operatorAction_leibniz, operatorAction_inv_unit, conjugate, add_mul,
    mul_neg, neg_mul, mul_assoc, Units.inv_mul_cancel_left]
  noncomm_ring

/-- The existing full gauge action on zero gives minus the right form. -/
theorem gaugeOneForm_zero_eq_neg_rightLogarithmicOneForm (g : Aˣ) :
    gaugeOneForm K (0 : OneForm K) g = -rightLogarithmicOneForm K g := by
  apply LinearMap.ext
  intro x
  simp only [gaugeOneForm_apply, rightLogarithmicOneForm_apply,
    LinearMap.zero_apply, LinearMap.neg_apply, mul_zero, zero_mul, zero_sub]

/-- Right Maurer--Cartan has a minus sign before the full commutator wedge. -/
theorem rightLogarithmicOneForm_maurerCartan (g : Aˣ) :
    exteriorDerivativeOne K (rightLogarithmicOneForm K g) =
      connectionWedgeSquare K (rightLogarithmicOneForm K g) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change exteriorDerivativeOne K (rightLogarithmicOneForm K g) x y =
    connectionWedgeSquare K (rightLogarithmicOneForm K g) x y
  have hflat : connectionCurvature K (gaugeOneForm K (0 : OneForm K) g) x y = 0 := by
    rw [connectionCurvature_gaugeOneForm]
    simp only [connectionCurvature_apply, LinearMap.zero_apply, map_zero,
      mul_zero, zero_mul, sub_self, zero_add, conjugate]
  rw [gaugeOneForm_zero_eq_neg_rightLogarithmicOneForm,
    connectionCurvature_apply] at hflat
  simp only [LinearMap.neg_apply, map_neg, neg_mul, mul_neg, neg_neg] at hflat
  rw [exteriorDerivativeOne_apply, connectionWedgeSquare_apply]
  apply sub_eq_zero.mp
  have hneg := congrArg Neg.neg hflat
  convert hneg using 1 <;> abel

end InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
