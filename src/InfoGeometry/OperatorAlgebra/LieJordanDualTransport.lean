/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.JordanMultiplicationClosure
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Dual Lie--Jordan transport on an associative algebra

The operators are native `Module.End`s. `LieAlgebra.ad` and the repository's
`jordanLeft` own their two summands. No commutation of the coefficients is
assumed. These are algebraic transport operators, not affine connections on a
statistical manifold, and the product formula is not a differential Laplacian.
-/

namespace InfoGeometry.OperatorAlgebra.LieJordanDualTransport

attribute [local instance 100] LieRing.ofAssociativeRing

open InfoGeometry.Core.JordanMultiplicationClosure
open InfoGeometry.Core.JordanAssociator

section NoncommScalars

variable {R A : Type*} [Ring R] [Ring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

/-- Associative adjoint endomorphism over any ring `[Ring R]`. -/
def ringAd (h : A) : Module.End R A :=
  LinearMap.mulLeft R h - LinearMap.mulRight R h

@[simp] theorem ringAd_apply (h x : A) :
    ringAd (R := R) h x = h * x - x * h := rfl

/-- Lie transport with a positive unnormalized Jordan summand over any `[Ring R]`. -/
def ringPlus (h s : A) : Module.End R A :=
  ringAd (R := R) h + jordanLeft (R := R) s

/-- Lie transport with the opposite Jordan summand over any `[Ring R]`. -/
def ringMinus (h s : A) : Module.End R A :=
  ringAd (R := R) h - jordanLeft (R := R) s

@[simp] theorem ringPlus_apply (h s x : A) :
    ringPlus (R := R) h s x = h * x - x * h + (s * x + x * s) := rfl

@[simp] theorem ringMinus_apply (h s x : A) :
    ringMinus (R := R) h s x = h * x - x * h - (s * x + x * s) := rfl

theorem ringPlus_add_ringMinus (h s : A) :
    ringPlus (R := R) h s + ringMinus (R := R) h s = 2 • ringAd (R := R) h := by
  unfold ringPlus ringMinus
  simp only [two_nsmul]
  abel

theorem ringPlus_sub_ringMinus (h s : A) :
    ringPlus (R := R) h s - ringMinus (R := R) h s = 2 • jordanLeft (R := R) s := by
  unfold ringPlus ringMinus
  simp only [two_nsmul]
  abel

/-- The mixed bracket is the Jordan operator of the coefficient commutator over any `[Ring R]`. -/
theorem ring_mixed_operator_commutator (h s : A) :
    ringAd (R := R) h * jordanLeft (R := R) s - jordanLeft (R := R) s * ringAd (R := R) h =
      jordanLeft (R := R) (h * s - s * h) := by
  ext x
  exact commutator_symm_operator h s x

theorem ringMinus_mul_ringPlus (h s : A) :
    ringMinus (R := R) h s * ringPlus (R := R) h s =
      ringAd (R := R) h * ringAd (R := R) h -
        jordanLeft (R := R) s * jordanLeft (R := R) s + jordanLeft (R := R) (h * s - s * h) := by
  calc
    _ = ringAd (R := R) h * ringAd (R := R) h -
          jordanLeft (R := R) s * jordanLeft (R := R) s +
          (ringAd (R := R) h * jordanLeft (R := R) s -
            jordanLeft (R := R) s * ringAd (R := R) h) := by
          unfold ringMinus ringPlus
          simp only [sub_mul, mul_add]
          abel
    _ = _ := by rw [ring_mixed_operator_commutator]

theorem ringPlus_mul_ringMinus (h s : A) :
    ringPlus (R := R) h s * ringMinus (R := R) h s =
      ringAd (R := R) h * ringAd (R := R) h -
        jordanLeft (R := R) s * jordanLeft (R := R) s - jordanLeft (R := R) (h * s - s * h) := by
  calc
    _ = ringAd (R := R) h * ringAd (R := R) h -
          jordanLeft (R := R) s * jordanLeft (R := R) s -
          (ringAd (R := R) h * jordanLeft (R := R) s -
            jordanLeft (R := R) s * ringAd (R := R) h) := by
          unfold ringMinus ringPlus
          simp only [mul_sub, add_mul]
          abel
    _ = _ := by rw [ring_mixed_operator_commutator]

theorem ring_product_order_defect (h s : A) :
    ringMinus (R := R) h s * ringPlus (R := R) h s - ringPlus (R := R) h s * ringMinus (R := R) h s =
      2 • jordanLeft (R := R) (h * s - s * h) := by
  rw [ringMinus_mul_ringPlus, ringPlus_mul_ringMinus]
  simp only [two_nsmul]
  abel

theorem ring_products_commute_iff (h s : A) :
    ringMinus (R := R) h s * ringPlus (R := R) h s = ringPlus (R := R) h s * ringMinus (R := R) h s ↔
      2 • jordanLeft (R := R) (h * s - s * h) = 0 := by
  rw [← sub_eq_zero, ring_product_order_defect]

theorem ringPlus_commutator (h s k t : A) :
    ringPlus (R := R) h s * ringPlus (R := R) k t - ringPlus (R := R) k t * ringPlus (R := R) h s =
      ringPlus (R := R) (h * k - k * h + (s * t - t * s))
        (h * t - t * h + (s * k - k * s)) := by
  ext x
  change (h * (k * x - x * k + (t * x + x * t)) -
      (k * x - x * k + (t * x + x * t)) * h +
      (s * (k * x - x * k + (t * x + x * t)) +
        (k * x - x * k + (t * x + x * t)) * s)) -
    (k * (h * x - x * h + (s * x + x * s)) -
      (h * x - x * h + (s * x + x * s)) * k +
      (t * (h * x - x * h + (s * x + x * s)) +
        (h * x - x * h + (s * x + x * s)) * t)) = _
  rw [ringPlus_apply]
  noncomm_ring

theorem ringPlus_leibniz_defect (h s x y : A) :
    ringPlus (R := R) h s (x * y) -
      (ringPlus (R := R) h s x * y + x * ringPlus (R := R) h s y) = -(2 • (x * s * y)) := by
  simp only [ringPlus_apply, two_nsmul]
  noncomm_ring

theorem map_ringPlus {B : Type*} [Ring B] [Module R B]
    [IsScalarTower R B B] [SMulCommClass R B B]
    (f : A →+* B) (h s x : A) :
    f (ringPlus (R := R) h s x) = ringPlus (R := R) (f h) (f s) (f x) := by
  simp only [ringPlus_apply, map_add, map_sub, map_mul]

theorem map_ringMinus {B : Type*} [Ring B] [Module R B]
    [IsScalarTower R B B] [SMulCommClass R B B]
    (f : A →+* B) (h s x : A) :
    f (ringMinus (R := R) h s x) = ringMinus (R := R) (f h) (f s) (f x) := by
  simp only [ringMinus_apply, map_add, map_sub, map_mul]

end NoncommScalars

section CommRingScalars

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Lie transport with a positive unnormalized Jordan summand. -/
def plus (h s : A) : Module.End R A :=
  LieAlgebra.ad R A h + jordanLeft (R := R) s

/-- Lie transport with the opposite Jordan summand. -/
def minus (h s : A) : Module.End R A :=
  LieAlgebra.ad R A h - jordanLeft (R := R) s

@[simp] theorem plus_apply (h s x : A) :
    plus (R := R) h s x = h * x - x * h + (s * x + x * s) := rfl

@[simp] theorem minus_apply (h s x : A) :
    minus (R := R) h s x = h * x - x * h - (s * x + x * s) := rfl

theorem plus_add_minus (h s : A) :
    plus (R := R) h s + minus (R := R) h s = 2 • LieAlgebra.ad R A h := by
  unfold plus minus
  simp only [two_nsmul]
  abel

theorem plus_sub_minus (h s : A) :
    plus (R := R) h s - minus (R := R) h s = 2 • jordanLeft (R := R) s := by
  unfold plus minus
  simp only [two_nsmul]
  abel

/-- The mixed bracket is the Jordan operator of the coefficient commutator. -/
theorem mixed_operator_commutator (h s : A) :
    LieAlgebra.ad R A h * jordanLeft (R := R) s - jordanLeft (R := R) s * LieAlgebra.ad R A h =
      jordanLeft (R := R) (h * s - s * h) := by
  ext x
  exact commutator_symm_operator h s x

/-- The correction has a plus sign for the order `minus * plus`. -/
theorem minus_mul_plus (h s : A) :
    minus (R := R) h s * plus (R := R) h s =
      LieAlgebra.ad R A h * LieAlgebra.ad R A h -
        jordanLeft (R := R) s * jordanLeft (R := R) s + jordanLeft (R := R) (h * s - s * h) := by
  calc
    _ = LieAlgebra.ad R A h * LieAlgebra.ad R A h -
          jordanLeft (R := R) s * jordanLeft (R := R) s +
          (LieAlgebra.ad R A h * jordanLeft (R := R) s -
            jordanLeft (R := R) s * LieAlgebra.ad R A h) := by
          unfold minus plus
          simp only [sub_mul, mul_add]
          abel
    _ = _ := by rw [mixed_operator_commutator]

/-- Reversing the composition reverses the mixed correction. -/
theorem plus_mul_minus (h s : A) :
    plus (R := R) h s * minus (R := R) h s =
      LieAlgebra.ad R A h * LieAlgebra.ad R A h -
        jordanLeft (R := R) s * jordanLeft (R := R) s - jordanLeft (R := R) (h * s - s * h) := by
  calc
    _ = LieAlgebra.ad R A h * LieAlgebra.ad R A h -
          jordanLeft (R := R) s * jordanLeft (R := R) s -
          (LieAlgebra.ad R A h * jordanLeft (R := R) s -
            jordanLeft (R := R) s * LieAlgebra.ad R A h) := by
          unfold minus plus
          simp only [mul_sub, add_mul]
          abel
    _ = _ := by rw [mixed_operator_commutator]

theorem product_order_defect (h s : A) :
    minus (R := R) h s * plus (R := R) h s - plus (R := R) h s * minus (R := R) h s =
      2 • jordanLeft (R := R) (h * s - s * h) := by
  rw [minus_mul_plus, plus_mul_minus]
  simp only [two_nsmul]
  abel

/-- Characteristic-free obstruction; no cancellation of two is hidden. -/
theorem products_commute_iff (h s : A) :
    minus (R := R) h s * plus (R := R) h s = plus (R := R) h s * minus (R := R) h s ↔
      2 • jordanLeft (R := R) (h * s - s * h) = 0 := by
  rw [← sub_eq_zero, product_order_defect]

/-- Algebraic curvature of two positive transports, retaining all cross terms. -/
theorem plus_commutator (h s k t : A) :
    plus (R := R) h s * plus (R := R) k t - plus (R := R) k t * plus (R := R) h s =
      plus (R := R) (h * k - k * h + (s * t - t * s))
        (h * t - t * h + (s * k - k * s)) := by
  ext x
  change (h * (k * x - x * k + (t * x + x * t)) -
      (k * x - x * k + (t * x + x * t)) * h +
      (s * (k * x - x * k + (t * x + x * t)) +
        (k * x - x * k + (t * x + x * t)) * s)) -
    (k * (h * x - x * h + (s * x + x * s)) -
      (h * x - x * h + (s * x + x * s)) * k +
      (t * (h * x - x * h + (s * x + x * s)) +
        (h * x - x * h + (s * x + x * s)) * t)) = _
  rw [plus_apply]
  noncomm_ring

/-- A Jordan perturbation has this exact failure of the associative Leibniz law. -/
theorem plus_leibniz_defect (h s x y : A) :
    plus (R := R) h s (x * y) -
      (plus (R := R) h s x * y + x * plus (R := R) h s y) = -(2 • (x * s * y)) := by
  simp only [plus_apply, two_nsmul]
  noncomm_ring

/-- Every ring homomorphism intertwines the evaluated transports. -/
theorem map_plus {B : Type*} [Ring B] [Algebra R B]
    (f : A →+* B) (h s x : A) :
    f (plus (R := R) h s x) = plus (R := R) (f h) (f s) (f x) := by
  simp only [plus_apply, map_add, map_sub, map_mul]

theorem map_minus {B : Type*} [Ring B] [Algebra R B]
    (f : A →+* B) (h s x : A) :
    f (minus (R := R) h s x) = minus (R := R) (f h) (f s) (f x) := by
  simp only [minus_apply, map_add, map_sub, map_mul]

end CommRingScalars

end InfoGeometry.OperatorAlgebra.LieJordanDualTransport
