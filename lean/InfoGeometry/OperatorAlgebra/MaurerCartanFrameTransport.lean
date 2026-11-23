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

section RingTransport

variable {A : Type*} [Ring A]

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

end RingTransport

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
    calc
      K.operatorAction x (↑g : A) * ↑g⁻¹ +
          (↑g : A) * K.operatorAction x (↑g⁻¹ : A) =
          K.operatorAction x ((↑g : A) * ↑g⁻¹) := by
            rw [K.operatorAction_leibniz]
      _ = 0 := by rw [Units.mul_inv]; exact action_one K x
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
  map_smul' c x := by simp

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

/-- The connection transforms actual operators, with no commuting approximation. -/
theorem covariant_frameTransport (g : Aˣ) (x : K.L) (a : A) :
    covariantDerivative K (gaugeForm K g) x (frameTransport g a) =
      frameTransport g (K.operatorAction x a) := by
  simp only [covariantDerivative, frameTransport, gaugeForm_apply]
  rw [K.operatorAction_leibniz x ((↑g⁻¹ : A) * a) (↑g : A)]
  rw [K.operatorAction_leibniz x (↑g⁻¹ : A) a]
  rw [action_inverse K x g]
  have hunit : (↑g : A) * (↑g⁻¹ : A) = 1 := Units.mul_inv g
  have hlast : (↑g⁻¹ : A) * a * ↑g *
      ((↑g⁻¹ : A) * K.operatorAction x (↑g : A)) =
      (↑g⁻¹ : A) * a * K.operatorAction x (↑g : A) := by
    calc
      (↑g⁻¹ : A) * a * ↑g *
          ((↑g⁻¹ : A) * K.operatorAction x (↑g : A)) =
          (↑g⁻¹ : A) * a * ((↑g : A) * (↑g⁻¹ : A)) *
            K.operatorAction x (↑g : A) := by noncomm_ring
      _ = (↑g⁻¹ : A) * a * K.operatorAction x (↑g : A) := by
        rw [hunit, mul_one]
  rw [hlast]
  noncomm_ring

/-- Constant charge or projector data become covariantly constant. -/
theorem covariant_frameTransport_zero (g : Aˣ) (x : K.L) (a : A)
    (ha : K.operatorAction x a = 0) :
    covariantDerivative K (gaugeForm K g) x (frameTransport g a) = 0 := by
  rw [covariant_frameTransport, ha]
  simp [frameTransport]

/-- Chevalley--Eilenberg curvature decomposition for a split one-form `θ = ϖ + e`:
when `θ` is flat and the odd covariant exterior derivative vanishes, horizontal curvature
satisfies Cartan's structural equation `R_ϖ(x, y) = -(e(x) e(y) - e(y) e(x))`. -/
theorem connectionCurvature_split_and_cartan_horizontal_from_flat
    (ϖ e : OneForm K) (x y : K.L) :
    (connectionCurvature K (ϖ + e) x y =
      (connectionCurvature K ϖ x y + (e x * e y - e y * e x)) +
        (exteriorDerivativeOne K e x y + (ϖ x * e y - e y * ϖ x) -
          (ϖ y * e x - e x * ϖ y))) ∧
    (connectionCurvature K (ϖ + e) x y = 0 →
      exteriorDerivativeOne K e x y + (ϖ x * e y - e y * ϖ x) -
        (ϖ y * e x - e x * ϖ y) = 0 →
      connectionCurvature K ϖ x y = -(e x * e y - e y * e x)) := by
  have hsplit :
      connectionCurvature K (ϖ + e) x y =
        (connectionCurvature K ϖ x y + (e x * e y - e y * e x)) +
          (exteriorDerivativeOne K e x y + (ϖ x * e y - e y * ϖ x) -
            (ϖ y * e x - e x * ϖ y)) := by
    simp only [connectionCurvature_apply, exteriorDerivativeOne_apply,
      LinearMap.add_apply, map_add]
    noncomm_ring
  refine ⟨hsplit, ?_⟩
  intro hflat hcov
  rw [hflat, hcov, add_zero] at hsplit
  exact eq_neg_of_add_eq_zero_left hsplit.symm

/-- For any Maurer--Cartan pure-gauge connection decomposed as `gaugeForm K g = ϖ + e`,
flatness (`gaugeForm_flat K g`) and vanishing odd covariant exterior derivative directly force
`R_ϖ(x, y) = -(e(x) e(y) - e(y) e(x))`. -/
theorem gaugeForm_split_cartan_horizontal_curvature
    (g : Aˣ) (ϖ e : OneForm K) (hge : gaugeForm K g = ϖ + e) (x y : K.L)
    (hcov : exteriorDerivativeOne K e x y + (ϖ x * e y - e y * ϖ x) -
      (ϖ y * e x - e x * ϖ y) = 0) :
    connectionCurvature K ϖ x y = -(e x * e y - e y * e x) := by
  have hflat : connectionCurvature K (ϖ + e) x y = 0 := by
    rw [← hge, gaugeForm_flat K g]
    rfl
  exact (connectionCurvature_split_and_cartan_horizontal_from_flat K ϖ e x y).2 hflat hcov

end InfoGeometry.OperatorAlgebra.MaurerCartanFrameTransport
