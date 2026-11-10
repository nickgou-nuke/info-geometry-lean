/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Algebraic identities for a formal bounded-transform factor

This file proves identities for a product `D * R` in an associative operator
algebra. It does not construct a bounded transform from an unbounded operator,
prove norm boundedness, or establish spectral-triple commutator estimates.
-/

namespace InfoGeometry.OperatorAlgebra.BoundedTransformSpectralTriple

/-- The square of the formal product `D * R` when its factors commute. -/
theorem boundedTransform_sq_eq_of_commute
    {A : Type*} [Semigroup A] (D R : A) (hcomm : D * R = R * D) :
    (D * R) * (D * R) = D * D * (R * R) := by
  calc
    (D * R) * (D * R) = D * ((R * D) * R) := by simp [mul_assoc]
    _ = D * ((D * R) * R) := by rw [hcomm]
    _ = D * D * (R * R) := by simp [mul_assoc]

/-- The defect of `D * R` reduces to the ordered product `D² R²` under commutation. -/
theorem boundedTransform_defect_eq_of_commute
    {A : Type*} [Ring A] (D R : A) (hcomm : D * R = R * D) :
    1 - (D * R) * (D * R) = 1 - (D * D) * (R * R) := by
  rw [boundedTransform_sq_eq_of_commute D R hcomm]

/-- The formal product `D * R` commutes with `R` when its factors commute. -/
theorem boundedTransform_commutes_with_resolvent_of_commute
    {A : Type*} [Semigroup A] (D R : A) (hcomm : D * R = R * D) :
    (D * R) * R = R * (D * R) := by
  calc
    (D * R) * R = (R * D) * R := by rw [hcomm]
    _ = R * (D * R) := by simp [mul_assoc]

/-- A left inverse and a right inverse of the same element coincide. -/
theorem left_eq_right_inverse
    {A : Type*} [Monoid A] (x left right : A)
    (hleft : left * x = 1) (hright : x * right = 1) :
    left = right := by
  calc
    left = left * 1 := by simp
    _ = left * (x * right) := by rw [hright]
    _ = (left * x) * right := by rw [mul_assoc]
    _ = 1 * right := by rw [hleft]
    _ = right := by simp

/-- The commutator with the formal transform product has the noncommutative
Leibniz expansion. -/
def commutator {A : Type*} [Ring A] (X Y : A) : A := X * Y - Y * X

theorem commutator_mul_left
    {A : Type*} [Ring A] (D R X : A) :
    commutator (D * R) X = D * commutator R X + commutator D X * R := by
  unfold commutator
  noncomm_ring

/-- A product of commuting self-adjoint factors is self-adjoint. -/
theorem selfAdjoint_mul_of_commute
    {A : Type*} [Ring A] [StarRing A] (D R : A)
    (hD : star D = D) (hR : star R = R) (hcomm : D * R = R * D) :
    star (D * R) = D * R := by
  calc
    star (D * R) = star R * star D := star_mul _ _
    _ = R * D := by rw [hR, hD]
    _ = D * R := hcomm.symm

end InfoGeometry.OperatorAlgebra.BoundedTransformSpectralTriple
