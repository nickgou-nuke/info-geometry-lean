/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
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

open InfoGeometry.Core.JordanMultiplicationClosure
open InfoGeometry.Core.JordanAssociator

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Lie transport with a positive unnormalized Jordan summand. -/
def plus (h s : A) : Module.End R A :=
  LieAlgebra.ad R A h + jordanLeft s

/-- Lie transport with the opposite Jordan summand. -/
def minus (h s : A) : Module.End R A :=
  LieAlgebra.ad R A h - jordanLeft s

@[simp] theorem plus_apply (h s x : A) :
    plus (R := R) h s x = h * x - x * h + (s * x + x * s) := rfl

@[simp] theorem minus_apply (h s x : A) :
    minus (R := R) h s x = h * x - x * h - (s * x + x * s) := rfl

theorem plus_add_minus (h s : A) :
    plus (R := R) h s + minus h s = 2 • LieAlgebra.ad R A h := by
  unfold plus minus
  simp only [two_nsmul]
  abel

theorem plus_sub_minus (h s : A) :
    plus (R := R) h s - minus h s = 2 • jordanLeft (R := R) s := by
  unfold plus minus
  simp only [two_nsmul]
  abel

/-- The mixed bracket is the Jordan operator of the coefficient commutator. -/
theorem mixed_operator_commutator (h s : A) :
    LieAlgebra.ad R A h * jordanLeft s - jordanLeft s * LieAlgebra.ad R A h =
      jordanLeft (R := R) (h * s - s * h) := by
  ext x
  exact commutator_symm_operator h s x

/-- The correction has a plus sign for the order `minus * plus`. -/
theorem minus_mul_plus (h s : A) :
    minus (R := R) h s * plus h s =
      LieAlgebra.ad R A h * LieAlgebra.ad R A h -
        jordanLeft s * jordanLeft s + jordanLeft (h * s - s * h) := by
  calc
    _ = LieAlgebra.ad R A h * LieAlgebra.ad R A h -
          jordanLeft s * jordanLeft s +
          (LieAlgebra.ad R A h * jordanLeft s -
            jordanLeft s * LieAlgebra.ad R A h) := by
          unfold minus plus
          noncomm_ring
    _ = _ := by rw [mixed_operator_commutator]

/-- Reversing the composition reverses the mixed correction. -/
theorem plus_mul_minus (h s : A) :
    plus (R := R) h s * minus h s =
      LieAlgebra.ad R A h * LieAlgebra.ad R A h -
        jordanLeft s * jordanLeft s - jordanLeft (h * s - s * h) := by
  calc
    _ = LieAlgebra.ad R A h * LieAlgebra.ad R A h -
          jordanLeft s * jordanLeft s -
          (LieAlgebra.ad R A h * jordanLeft s -
            jordanLeft s * LieAlgebra.ad R A h) := by
          unfold minus plus
          noncomm_ring
    _ = _ := by rw [mixed_operator_commutator]

theorem product_order_defect (h s : A) :
    minus (R := R) h s * plus h s - plus h s * minus h s =
      2 • jordanLeft (R := R) (h * s - s * h) := by
  rw [minus_mul_plus, plus_mul_minus]
  simp only [two_nsmul]
  abel

/-- Characteristic-free obstruction; no cancellation of two is hidden. -/
theorem products_commute_iff (h s : A) :
    minus (R := R) h s * plus h s = plus h s * minus h s ↔
      2 • jordanLeft (R := R) (h * s - s * h) = 0 := by
  rw [← sub_eq_zero, product_order_defect]

/-- Algebraic curvature of two positive transports, retaining all cross terms. -/
theorem plus_commutator (h s k t : A) :
    plus (R := R) h s * plus k t - plus k t * plus h s =
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
      (plus h s x * y + x * plus h s y) = -(2 • (x * s * y)) := by
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

end InfoGeometry.OperatorAlgebra.LieJordanDualTransport
