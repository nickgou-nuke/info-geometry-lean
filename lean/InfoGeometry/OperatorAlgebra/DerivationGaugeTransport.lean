/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
import InfoGeometry.Geometry.AssociativeGaugeConnection
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Gauge transport for derivation-based noncommutative connections

The existing native Chevalley--Eilenberg curvature is transported without
assuming that its derivation directions commute.  Exact curvature covariance
is proved through the faithful left regular module action; the adjoint action
alone would determine curvature only modulo the center.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

open InfoGeometry.Algebra
open InfoGeometry.Algebra.DerivationLieLane

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable (K : DerivationLieLane R A)

/-- The fundamental connection on the regular right module, bundled in the
native endomorphism algebra. -/
def fundamentalCovariantDerivative (Γ : OneForm K) :
    K.L →ₗ[R] Module.End R A :=
  K.operatorAction + (LinearMap.mul R A).comp Γ

@[simp] theorem fundamentalCovariantDerivative_apply
    (Γ : OneForm K) (x : K.L) (a : A) :
    fundamentalCovariantDerivative K Γ x a =
      K.operatorAction x a + Γ x * a := rfl

/-- The fundamental connection obeys the right-module connection rule. -/
theorem fundamentalCovariantDerivative_leibniz
    (Γ : OneForm K) (x : K.L) (a b : A) :
    fundamentalCovariantDerivative K Γ x (a * b) =
      fundamentalCovariantDerivative K Γ x a * b +
        a * K.operatorAction x b := by
  exact InfoGeometry.Geometry.AssociativeGaugeConnection.connection_leibniz
    (K.operatorAction x) (K.operatorAction_leibniz x) (Γ x) a b

/-- The correction by the Lie bracket of derivation directions is essential. -/
theorem fundamentalCovariantDerivative_commutator
    (Γ : OneForm K) (x y : K.L) (a : A) :
    fundamentalCovariantDerivative K Γ x
        (fundamentalCovariantDerivative K Γ y a) -
      fundamentalCovariantDerivative K Γ y
        (fundamentalCovariantDerivative K Γ x a) -
      fundamentalCovariantDerivative K Γ ⁅x, y⁆ a =
        connectionCurvature K Γ x y * a := by
  simp only [fundamentalCovariantDerivative_apply, map_add]
  rw [K.operatorAction_leibniz x (Γ y) a,
    K.operatorAction_leibniz y (Γ x) a,
    K.operatorAction_commutator_apply x y a, connectionCurvature_apply]
  noncomm_ring

/-- Curvature as an equality in the genuine noncommutative endomorphism algebra. -/
theorem fundamentalCovariantDerivative_commutator_eq
    (Γ : OneForm K) (x y : K.L) :
    ⁅fundamentalCovariantDerivative K Γ x,
      fundamentalCovariantDerivative K Γ y⁆ -
        fundamentalCovariantDerivative K Γ ⁅x, y⁆ =
      LinearMap.mulLeft R (connectionCurvature K Γ x y) := by
  apply LinearMap.ext
  intro a
  exact fundamentalCovariantDerivative_commutator K Γ x y a

/-- A gauge transform includes the inhomogeneous derivative term. -/
def gaugeOneForm (Γ : OneForm K) (u : Aˣ) : OneForm K :=
  (LinearMap.mulRight R (↑u⁻¹ : A)).comp
    ((LinearMap.mulLeft R (u : A)).comp Γ - exteriorDerivativeZero K (u : A))

@[simp] theorem gaugeOneForm_apply (Γ : OneForm K) (u : Aˣ) (x : K.L) :
    gaugeOneForm K Γ u x =
      (u : A) * Γ x * (↑u⁻¹ : A) -
        K.operatorAction x (u : A) * (↑u⁻¹ : A) := by
  change ((u : A) * Γ x - K.operatorAction x (u : A)) * (↑u⁻¹ : A) = _
  exact sub_mul _ _ _

theorem fundamentalCovariantDerivative_gauge_intertwine
    (Γ : OneForm K) (u : Aˣ) (x : K.L) (a : A) :
    fundamentalCovariantDerivative K (gaugeOneForm K Γ u) x ((u : A) * a) =
      (u : A) * fundamentalCovariantDerivative K Γ x a := by
  simpa only [fundamentalCovariantDerivative_apply, gaugeOneForm_apply,
    InfoGeometry.Geometry.AssociativeGaugeConnection.covariantDerivative_apply,
    InfoGeometry.Geometry.AssociativeGaugeConnection.gaugePotential,
    InfoGeometry.Geometry.AssociativeGaugeConnection.conjugate] using
    InfoGeometry.Geometry.AssociativeGaugeConnection.gauge_intertwine
      (K.operatorAction x) (K.operatorAction_leibniz x) (Γ x) u a

/-- Gauge transport is Mathlib's native Lie conjugation of endomorphisms. -/
theorem fundamentalCovariantDerivative_gauge_conj
    (Γ : OneForm K) (u : Aˣ) (x : K.L) :
    fundamentalCovariantDerivative K (gaugeOneForm K Γ u) x =
      (u.mulLeftLinearEquiv R A).lieConj
        (fundamentalCovariantDerivative K Γ x) := by
  apply LinearMap.ext
  intro a
  have h := fundamentalCovariantDerivative_gauge_intertwine K Γ u x
    ((↑u⁻¹ : A) * a)
  simpa only [Units.mul_inv_cancel_left, LinearEquiv.lieConj_apply,
    LinearEquiv.conj_apply_apply, Units.mulLeftLinearEquiv_apply,
    Units.symm_mulLeftLinearEquiv_apply] using h

/-- Exact curvature covariance, including possible central curvature. -/
theorem connectionCurvature_gaugeOneForm
    (Γ : OneForm K) (u : Aˣ) (x y : K.L) :
    connectionCurvature K (gaugeOneForm K Γ u) x y =
      InfoGeometry.Geometry.AssociativeGaugeConnection.conjugate u
        (connectionCurvature K Γ x y) := by
  have haction (a : A) :
      connectionCurvature K (gaugeOneForm K Γ u) x y * ((u : A) * a) =
        (u : A) * (connectionCurvature K Γ x y * a) := by
    calc
      _ = fundamentalCovariantDerivative K (gaugeOneForm K Γ u) x
            (fundamentalCovariantDerivative K (gaugeOneForm K Γ u) y ((u : A) * a)) -
          fundamentalCovariantDerivative K (gaugeOneForm K Γ u) y
            (fundamentalCovariantDerivative K (gaugeOneForm K Γ u) x ((u : A) * a)) -
          fundamentalCovariantDerivative K (gaugeOneForm K Γ u) ⁅x, y⁆ ((u : A) * a) :=
        (fundamentalCovariantDerivative_commutator K (gaugeOneForm K Γ u) x y _).symm
      _ = (u : A) *
          (fundamentalCovariantDerivative K Γ x (fundamentalCovariantDerivative K Γ y a) -
            fundamentalCovariantDerivative K Γ y (fundamentalCovariantDerivative K Γ x a) -
              fundamentalCovariantDerivative K Γ ⁅x, y⁆ a) := by
        simp only [fundamentalCovariantDerivative_gauge_intertwine, mul_sub]
      _ = _ := by rw [fundamentalCovariantDerivative_commutator]
  simpa only [Units.mul_inv, mul_one,
    InfoGeometry.Geometry.AssociativeGaugeConnection.conjugate, mul_assoc]
    using haction (↑u⁻¹ : A)

@[simp] theorem operatorAction_one (x : K.L) :
    K.operatorAction x (1 : A) = 0 := by
  have h := K.operatorAction_leibniz x (1 : A) 1
  simp only [one_mul, mul_one] at h
  exact add_eq_left.mp h.symm

/-- Differentiating the inverse uses the noncommutative order shown here. -/
theorem operatorAction_inv_unit (u : Aˣ) (x : K.L) :
    K.operatorAction x (↑u⁻¹ : A) =
      -((↑u⁻¹ : A) * K.operatorAction x (u : A) * (↑u⁻¹ : A)) := by
  have h : K.operatorAction x (u : A) * (↑u⁻¹ : A) +
      (u : A) * K.operatorAction x (↑u⁻¹ : A) = 0 := by
    rw [← K.operatorAction_leibniz, Units.mul_inv, operatorAction_one]
  have hh := congrArg (fun a : A => (↑u⁻¹ : A) * a) h
  simp only [mul_add, mul_zero, ← mul_assoc, Units.inv_mul, one_mul] at hh
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [add_comm] using hh

@[simp] theorem gaugeOneForm_one (Γ : OneForm K) :
    gaugeOneForm K Γ 1 = Γ := by
  apply LinearMap.ext
  intro x
  simp only [gaugeOneForm_apply, inv_one, Units.val_one, one_mul,
    mul_one, operatorAction_one, sub_zero]

/-- The composition order is that of the left gauge action. -/
theorem gaugeOneForm_mul (Γ : OneForm K) (u v : Aˣ) :
    gaugeOneForm K (gaugeOneForm K Γ v) u =
      gaugeOneForm K Γ (u * v) := by
  apply LinearMap.ext
  intro x
  simp only [gaugeOneForm_apply, Units.val_mul, mul_inv_rev,
    K.operatorAction_leibniz, mul_sub, sub_mul, add_mul,
    mul_assoc, Units.mul_inv_cancel_left]
  abel

@[simp] theorem gaugeOneForm_inv (Γ : OneForm K) (u : Aˣ) :
    gaugeOneForm K (gaugeOneForm K Γ u) u⁻¹ = Γ := by
  rw [gaugeOneForm_mul, inv_mul_cancel, gaugeOneForm_one]

/-- Gauge transport is an equivalence of the native one-form carrier. -/
def gaugeOneFormEquiv (u : Aˣ) : OneForm K ≃ OneForm K where
  toFun := fun Γ => gaugeOneForm K Γ u
  invFun := fun Γ => gaugeOneForm K Γ u⁻¹
  left_inv := fun Γ => gaugeOneForm_inv K Γ u
  right_inv := fun Γ => by
    simpa only [inv_inv] using gaugeOneForm_inv K Γ u⁻¹

/-- The adjoint connection transforms by the same full gauge action. -/
theorem covariantDerivative_gaugeOneForm
    (Γ : OneForm K) (u : Aˣ) (x : K.L) (a : A) :
    covariantDerivative K (gaugeOneForm K Γ u) x
        (InfoGeometry.Geometry.AssociativeGaugeConnection.conjugate u a) =
      InfoGeometry.Geometry.AssociativeGaugeConnection.conjugate u
        (covariantDerivative K Γ x a) := by
  simp only [covariantDerivative, gaugeOneForm_apply,
    InfoGeometry.Geometry.AssociativeGaugeConnection.conjugate,
    K.operatorAction_leibniz, operatorAction_inv_unit,
    mul_add, add_mul, mul_sub, sub_mul, mul_neg, mul_assoc,
    Units.inv_mul_cancel_left]
  noncomm_ring

/-- Flatness is invariant in both directions under gauge transport. -/
theorem connectionCurvature_gaugeOneForm_eq_zero_iff
    (Γ : OneForm K) (u : Aˣ) :
    connectionCurvature K (gaugeOneForm K Γ u) = 0 ↔
      connectionCurvature K Γ = 0 := by
  constructor
  · intro h
    apply DFunLike.ext
    intro x
    apply LinearMap.ext
    intro y
    change connectionCurvature K Γ x y = (0 : A)
    have hh : connectionCurvature K (gaugeOneForm K Γ u) x y = 0 := by
      rw [h]
      rfl
    rw [connectionCurvature_gaugeOneForm] at hh
    have hh' := congrArg (fun a : A => (↑u⁻¹ : A) * a * (u : A)) hh
    simpa [InfoGeometry.Geometry.AssociativeGaugeConnection.conjugate, mul_assoc] using hh'
  · intro h
    apply DFunLike.ext
    intro x
    apply LinearMap.ext
    intro y
    change connectionCurvature K (gaugeOneForm K Γ u) x y = (0 : A)
    rw [connectionCurvature_gaugeOneForm, h]
    change InfoGeometry.Geometry.AssociativeGaugeConnection.conjugate u (0 : A) = 0
    simp [InfoGeometry.Geometry.AssociativeGaugeConnection.conjugate]

end InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
