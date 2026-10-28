/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.OperatorBerezinianCore
import InfoGeometry.OperatorAlgebra.DerivationRightLogarithmicForm
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Tactic.NoncommRing

/-!
# Ordered operator Berezinian and its native logarithmic differential

This module uses the existing `SplitQuaternion.opNoncommBerezinian` and its
existing inverse. The ratio is identified with its actual unit product,
transforms covariantly under simultaneous conjugation, and has an exact
commutator defect of multiplicativity. Its logarithmic derivative is the
native right one-form of that same unit.
-/

noncomputable section

namespace InfoGeometry.Canonical.OperatorBerezinianDifferential

open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion
open InfoGeometry.Algebra
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

variable {A : Type*} [Ring A]

/-- The existing operator ratio is the value of the ordered unit product. -/
theorem opNoncommBerezinian_eq_unit (u Δ : Aˣ) :
    opNoncommBerezinian u Δ = (↑(u * Δ⁻¹) : A) := rfl

/-- The existing inverse is exactly the inverse of that unit product. -/
theorem opNoncommBerezinianInv_eq_unit_inv (u Δ : Aˣ) :
    opNoncommBerezinianInv u Δ = (↑((u * Δ⁻¹)⁻¹) : A) := by
  simp only [opNoncommBerezinianInv, mul_inv_rev, inv_inv, Units.val_mul]

theorem opNoncommBerezinian_isUnit (u Δ : Aˣ) :
    IsUnit (opNoncommBerezinian u Δ) := by
  rw [opNoncommBerezinian_eq_unit]
  exact (u * Δ⁻¹).isUnit

/-- Conjugating both unit parameters conjugates the ordered ratio. -/
theorem opNoncommBerezinian_conjugate (g u Δ : Aˣ) :
    opNoncommBerezinian (g * u * g⁻¹) (g * Δ * g⁻¹) =
      (g : A) * opNoncommBerezinian u Δ * (↑g⁻¹ : A) := by
  simp only [opNoncommBerezinian, mul_inv_rev, inv_inv, Units.val_mul,
    mul_assoc, Units.inv_mul_cancel_left]

/-- Failure of multiplicativity is precisely this ordered commutator. -/
theorem opNoncommBerezinian_mul_defect (u₁ u₂ Δ₁ Δ₂ : Aˣ) :
    opNoncommBerezinian (u₁ * u₂) (Δ₁ * Δ₂) -
        opNoncommBerezinian u₁ Δ₁ * opNoncommBerezinian u₂ Δ₂ =
      (u₁ : A) *
        (opNoncommBerezinian u₂ Δ₂ * (↑Δ₁⁻¹ : A) -
          (↑Δ₁⁻¹ : A) * opNoncommBerezinian u₂ Δ₂) := by
  simp only [opNoncommBerezinian, mul_inv_rev, Units.val_mul]
  noncomm_ring

/-- This commutation condition is necessary and sufficient for the product law. -/
theorem opNoncommBerezinian_mul_eq_iff (u₁ u₂ Δ₁ Δ₂ : Aˣ) :
    opNoncommBerezinian (u₁ * u₂) (Δ₁ * Δ₂) =
        opNoncommBerezinian u₁ Δ₁ * opNoncommBerezinian u₂ Δ₂ ↔
      Commute (opNoncommBerezinian u₂ Δ₂) (↑Δ₁⁻¹ : A) := by
  constructor
  · intro h
    have hz := sub_eq_zero.mpr h
    rw [opNoncommBerezinian_mul_defect] at hz
    have hc := congrArg (fun a : A => (↑u₁⁻¹ : A) * a) hz
    simp only [Units.inv_mul_cancel_left, mul_zero] at hc
    exact sub_eq_zero.mp hc
  · intro h
    apply sub_eq_zero.mp
    rw [opNoncommBerezinian_mul_defect]
    change opNoncommBerezinian u₂ Δ₂ * (↑Δ₁⁻¹ : A) =
      (↑Δ₁⁻¹ : A) * opNoncommBerezinian u₂ Δ₂ at h
    rw [h, sub_self, mul_zero]

section Differential

variable {R : Type*} [CommRing R] [Algebra R A]
variable (K : DerivationLieLane R A)

/-- Differentiating the actual ratio and multiplying by its actual inverse
is the native logarithmic one-form of its unit. -/
theorem opNoncommBerezinian_logarithmicOneForm (u Δ : Aˣ) :
    (LinearMap.mulRight R (opNoncommBerezinianInv u Δ)).comp
        (exteriorDerivativeZero K (opNoncommBerezinian u Δ)) =
      rightLogarithmicOneForm K (u * Δ⁻¹) := by
  rw [opNoncommBerezinian_eq_unit, opNoncommBerezinianInv_eq_unit_inv]
  rfl

/-- The logarithmic derivative retains conjugation by the entire ordered ratio. -/
theorem opNoncommBerezinian_logarithmicDerivative
    (u Δ : Aˣ) (x : K.L) :
    K.operatorAction x (opNoncommBerezinian u Δ) *
        opNoncommBerezinianInv u Δ =
      rightLogarithmicOneForm K u x -
        opNoncommBerezinian u Δ * rightLogarithmicOneForm K Δ x *
          opNoncommBerezinianInv u Δ := by
  simpa only [rightLogarithmicOneForm_apply,
    InfoGeometry.Geometry.AssociativeGaugeConnection.conjugate,
    opNoncommBerezinian_eq_unit, opNoncommBerezinianInv_eq_unit_inv]
    using rightLogarithmicOneForm_mul_inv K u Δ x

end Differential

end InfoGeometry.Canonical.OperatorBerezinianDifferential
