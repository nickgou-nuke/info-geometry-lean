/-
InfoGeometry/Geometry/ConstructiveCauchyKernel.lean
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Geometry.ConstructiveCauchyKernel

noncomputable def unitInverse {Value : Type*} [Monoid Value]
    {Z : Value} (hZ : IsUnit Z) : Value :=
  ↑(hZ.unit⁻¹)

theorem unitInverse_left_inv {Value : Type*} [Monoid Value]
    {Z : Value} (hZ : IsUnit Z) :
    unitInverse hZ * Z = 1 := by
  calc
    unitInverse hZ * Z = unitInverse hZ * (↑hZ.unit : Value) := by
      exact congrArg (fun x : Value => unitInverse hZ * x) hZ.unit_spec.symm
    _ = 1 := by simp [unitInverse]

theorem unitInverse_right_inv {Value : Type*} [Monoid Value]
    {Z : Value} (hZ : IsUnit Z) :
    Z * unitInverse hZ = 1 := by
  calc
    Z * unitInverse hZ = (↑hZ.unit : Value) * unitInverse hZ := by
      exact congrArg (fun x : Value => x * unitInverse hZ) hZ.unit_spec.symm
    _ = 1 := by simp [unitInverse]

theorem resolvent_identity {Value : Type*} [Ring Value]
    (A B : Value)
    (hA : IsUnit A)
    (hB : IsUnit B) :
    unitInverse hA - unitInverse hB =
      unitInverse hA * (B - A) * unitInverse hB := by
  calc
    unitInverse hA - unitInverse hB
        = unitInverse hA * 1 - 1 * unitInverse hB := by
          rw [mul_one, one_mul]
    _ = unitInverse hA * (B * unitInverse hB) -
          (unitInverse hA * A) * unitInverse hB := by
          rw [unitInverse_right_inv hB, unitInverse_left_inv hA]
    _ = unitInverse hA * B * unitInverse hB -
          unitInverse hA * A * unitInverse hB := by
          rw [← mul_assoc]
    _ = (unitInverse hA * B - unitInverse hA * A) * unitInverse hB := by
          rw [sub_mul]
    _ = unitInverse hA * (B - A) * unitInverse hB := by
          rw [mul_sub]

/-! ## Scalar field resolvents -/

/--
Scalar resolvent identity, with the inverse laws discharged by field inversion.
-/
theorem scalar_resolvent_identity {K : Type*} [Field K]
    (A B : K)
    (hA : A ≠ 0)
    (hB : B ≠ 0) :
    A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ := by
  field_simp

/-- The resolvent identity specializes to the zero difference when the points coincide. -/
theorem scalar_resolvent_identity_self {K : Type*} [Field K]
    (A : K) :
    A⁻¹ - A⁻¹ = A⁻¹ * (A - A) * A⁻¹ := by
  simp

/-- The scalar inverse-difference specialization of the resolvent identity. -/
theorem scalar_inverse_difference {K : Type*} [Field K]
    (A B : K)
    (hA : A ≠ 0)
    (hB : B ≠ 0) :
    A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ := by
  exact scalar_resolvent_identity A B hA hB

/-- The bundled scalar inverse is left-inverse to the scalar. -/
theorem scalarVerifiedInverse_left_inv {K : Type*} [Field K]
    (z : K) (hz : z ≠ 0) :
    z⁻¹ * z = 1 := by
  exact inv_mul_cancel₀ hz

/-- The bundled scalar inverse is right-inverse to the scalar. -/
theorem scalarVerifiedInverse_right_inv {K : Type*} [Field K]
    (z : K) (hz : z ≠ 0) :
    z * z⁻¹ = 1 := by
  exact mul_inv_cancel₀ hz

end InfoGeometry.Geometry.ConstructiveCauchyKernel
