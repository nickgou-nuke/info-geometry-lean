/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

/-!
# Constructed Maurer--Cartan frames in a noncommutative algebra

The existing native Chevalley--Eilenberg differential is used unchanged.
For a genuine unit g, the form g^-1 D(g) is constructed and its flatness
is proved, including the bracket of derivation directions. Covariant
transport is an exact identity, not an assumed compatibility field.
-/

namespace InfoGeometry.OperatorAlgebra.MaurerCartanFrameTransport

open InfoGeometry.Algebra
open InfoGeometry.Algebra.DerivationLieLane
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable (K : DerivationLieLane R A)

/-- Every represented Leibniz operator kills the unit. -/
theorem action_one (x : K.L) : K.operatorAction x (1 : A) = 0 := by
  have h := K.operatorAction_leibniz x (1 : A) 1
  simp only [mul_one, one_mul] at h
  have hh : K.operatorAction x 1 + K.operatorAction x 1 = K.operatorAction x 1 + 0 := by
    simpa using h.symm
  exact add_left_cancel hh

/-- Inverse differentiation with the noncommutative order retained. -/
theorem action_inverse (x : K.L) (g : Aˣ) :
    K.operatorAction x (↑g⁻¹ : A) =
      -(↑g⁻¹ * K.operatorAction x (↑g : A) * ↑g⁻¹) := by
  have h : K.operatorAction x (↑g : A) * ↑g⁻¹ +
      (↑g : A) * K.operatorAction x (↑g⁻¹ : A) = 0 := by
    have hder := K.operatorAction_leibniz x (↑g : A) (↑g⁻¹ : A)
    rw [Units.mul_inv, action_one] at hder
    simpa using hder.symm
  have hh := congrArg (fun z : A => (↑g⁻¹ : A) * z) h
  simp only [mul_add, ← mul_assoc, Units.inv_mul, one_mul, mul_zero] at hh
  calc K.operatorAction x (↑g⁻¹ : A) =
      (↑g⁻¹ * K.operatorAction x (↑g : A) * ↑g⁻¹ +
        K.operatorAction x (↑g⁻¹ : A)) -
          ↑g⁻¹ * K.operatorAction x (↑g : A) * ↑g⁻¹ := by abel
    _ = _ := by rw [hh, zero_sub]

/-- A genuine operator-valued one-form on the existing Lie lane. -/
def gaugeForm (g : Aˣ) : OneForm K where
  toFun x := (↑g⁻¹ : A) * K.operatorAction x (↑g : A)
  map_add' x y := by simp [mul_add]
  map_smul' c x := by simp [mul_smul_comm]

@[simp] theorem gaugeForm_apply (g : Aˣ) (x : K.L) :
    gaugeForm K g x = (↑g⁻¹ : A) * K.operatorAction x (↑g : A) := rfl

/-- The nonabelian product law for logarithmic derivatives. -/
theorem gaugeForm_product (g h : Aˣ) (x : K.L) :
    gaugeForm K (g * h) x =
      (↑h⁻¹ : A) * gaugeForm K g x * ↑h + gaugeForm K h x := by
  simp [gaugeForm, K.operatorAction_leibniz, mul_add, mul_assoc]

/-- Maurer--Cartan is derived, not added as a hypothesis. -/
theorem gaugeForm_flat (g : Aˣ) : connectionCurvature K (gaugeForm K g) = 0 := by
  apply Subtype.ext
  ext x y
  change connectionCurvature K (gaugeForm K g) x y = 0
  rw [connectionCurvature_apply]
  simp only [gaugeForm_apply, K.operatorAction_leibniz,
    action_inverse, K.operatorAction_commutator_apply]
  noncomm_ring

/-- Coordinate transport of an algebra element by the frame unit. -/
def frameTransport (g : Aˣ) (a : A) : A := (↑g⁻¹ : A) * a * ↑g

theorem frameTransport_mul (g : Aˣ) (a b : A) :
    frameTransport g (a * b) = frameTransport g a * frameTransport g b := by
  simp [frameTransport, mul_assoc]

theorem frameTransport_idempotent (g : Aˣ) (p : A) (hp : p * p = p) :
    frameTransport g p * frameTransport g p = frameTransport g p := by
  rw [← frameTransport_mul, hp]

theorem frameTransport_square_zero (g : Aˣ) (a : A) (ha : a * a = 0) :
    frameTransport g a * frameTransport g a = 0 := by
  rw [← frameTransport_mul, ha]
  simp [frameTransport]

/-- The connection transforms actual operators, with no commuting approximation. -/
theorem covariant_frameTransport (g : Aˣ) (x : K.L) (a : A) :
    covariantDerivative K (gaugeForm K g) x (frameTransport g a) =
      frameTransport g (K.operatorAction x a) := by
  change K.operatorAction x ((↑g⁻¹ : A) * a * ↑g) +
      ((↑g⁻¹ : A) * K.operatorAction x (↑g : A)) *
        ((↑g⁻¹ : A) * a * ↑g) -
      ((↑g⁻¹ : A) * a * ↑g) *
        ((↑g⁻¹ : A) * K.operatorAction x (↑g : A)) =
    (↑g⁻¹ : A) * K.operatorAction x a * ↑g
  rw [K.operatorAction_leibniz x ((↑g⁻¹ : A) * a) (↑g),
    K.operatorAction_leibniz x (↑g⁻¹ : A) a, action_inverse]
  simp [mul_assoc, Units.inv_mul, Units.mul_inv]
  noncomm_ring

/-- Constant charge or projector data become covariantly constant. -/
theorem covariant_frameTransport_zero (g : Aˣ) (x : K.L) (a : A)
    (ha : K.operatorAction x a = 0) :
    covariantDerivative K (gaugeForm K g) x (frameTransport g a) = 0 := by
  rw [covariant_frameTransport, ha]
  simp [frameTransport]

end InfoGeometry.OperatorAlgebra.MaurerCartanFrameTransport
