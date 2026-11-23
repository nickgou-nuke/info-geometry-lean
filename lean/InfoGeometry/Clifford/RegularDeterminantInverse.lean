/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Determinant

/-!
# Regular determinant criterion for algebra inverses

For a finite-dimensional real algebra, left multiplication is an intrinsic
linear endomorphism. Its determinant is basis-independent and detects exactly
which elements are units. This gives a coordinate-free inverse-existence
criterion that applies in particular to finite-dimensional real Clifford
algebras.

This regular determinant has degree `finrank ℝ A`; it is not identified here
with Shirokov's reduced Clifford determinant or his scalar-part recurrence.
-/

namespace InfoGeometry.Clifford.RegularDeterminantInverse

variable {A : Type*} [Ring A] [Algebra ℝ A] [FiniteDimensional ℝ A]

/-- The left regular action of `a` on its algebra, as an `ℝ`-linear map. -/
def leftRegularMap (a : A) : A →ₗ[ℝ] A := Algebra.lmul ℝ A a

/-- Basis-independent regular determinant: the determinant of left
multiplication by the algebra element. -/
noncomputable def regularDeterminant (a : A) : ℝ :=
  (leftRegularMap a).det

/-- The regular determinant is a unit exactly when the algebra element is a
unit. -/
theorem isUnit_regularDeterminant_iff (a : A) :
    IsUnit (regularDeterminant a) ↔ IsUnit a := by
  rw [regularDeterminant, ← Algebra.lmul_isUnit_iff]
  exact LinearMap.isUnit_iff_isUnit_det (leftRegularMap a)

/-- Over `ℝ`, nonvanishing of the regular determinant is equivalent to
invertibility of the algebra element. -/
theorem regularDeterminant_ne_zero_iff (a : A) :
    regularDeterminant a ≠ 0 ↔ IsUnit a := by
  rw [← isUnit_iff_ne_zero, isUnit_regularDeterminant_iff]

/-- A nonzero regular determinant therefore constructs a genuine two-sided
algebra inverse. -/
noncomputable def inverseOfNonzeroRegularDeterminant
    (a : A) (h : regularDeterminant a ≠ 0) : A :=
  ((((regularDeterminant_ne_zero_iff a).mp h).unit)⁻¹ : Aˣ)

theorem inverseOfNonzeroRegularDeterminant_mul
    (a : A) (h : regularDeterminant a ≠ 0) :
    inverseOfNonzeroRegularDeterminant a h * a = 1 := by
  change (((regularDeterminant_ne_zero_iff a).mp h).unit⁻¹ : Aˣ) *
    (((regularDeterminant_ne_zero_iff a).mp h).unit : Aˣ) = 1
  simp

theorem mul_inverseOfNonzeroRegularDeterminant
    (a : A) (h : regularDeterminant a ≠ 0) :
    a * inverseOfNonzeroRegularDeterminant a h = 1 := by
  change (((regularDeterminant_ne_zero_iff a).mp h).unit : Aˣ) *
    (((regularDeterminant_ne_zero_iff a).mp h).unit⁻¹ : Aˣ) = 1
  simp

end InfoGeometry.Clifford.RegularDeterminantInverse
