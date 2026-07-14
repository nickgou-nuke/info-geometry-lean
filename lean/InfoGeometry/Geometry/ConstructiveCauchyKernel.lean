/-
InfoGeometry/Geometry/ConstructiveCauchyKernel.lean
-/

import Mathlib

noncomputable section

namespace ConstructiveCauchyKernel

structure VerifiedInverse {Value : Type*} [Ring Value] (Z : Value) where
  inv : Value
  left_inv : inv * Z = 1
  right_inv : Z * inv = 1

theorem resolvent_identity {Value : Type*} [Ring Value]
    (A B : Value)
    (invA : VerifiedInverse A)
    (invB : VerifiedInverse B) :
    invA.inv - invB.inv = invA.inv * (B - A) * invB.inv := by
  calc
    invA.inv - invB.inv
        = invA.inv * 1 - 1 * invB.inv := by
          rw [mul_one, one_mul]
    _ = invA.inv * (B * invB.inv) - (invA.inv * A) * invB.inv := by
          rw [invB.right_inv, invA.left_inv]
    _ = invA.inv * B * invB.inv - invA.inv * A * invB.inv := by
          rw [← mul_assoc]
    _ = (invA.inv * B - invA.inv * A) * invB.inv := by
          rw [sub_mul]
    _ = invA.inv * (B - A) * invB.inv := by
          rw [mul_sub]

/-! ## Scalar field resolvents -/

/--
In a field, a nonzero element has a constructively verified two-sided inverse.
-/
def scalarVerifiedInverse {K : Type*} [Field K]
    (z : K)
    (hz : z ≠ 0) :
    VerifiedInverse z where
  inv := z⁻¹
  left_inv := by
    exact inv_mul_cancel₀ hz
  right_inv := by
    exact mul_inv_cancel₀ hz

/--
Scalar resolvent identity, with the inverse laws discharged by field inversion.
-/
theorem scalar_resolvent_identity {K : Type*} [Field K]
    (A B : K)
    (hA : A ≠ 0)
    (hB : B ≠ 0) :
    A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ := by
  exact resolvent_identity A B (scalarVerifiedInverse A hA) (scalarVerifiedInverse B hB)

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
    (scalarVerifiedInverse z hz).inv * z = 1 := by
  simpa [scalarVerifiedInverse] using inv_mul_cancel₀ hz

/-- The bundled scalar inverse is right-inverse to the scalar. -/
theorem scalarVerifiedInverse_right_inv {K : Type*} [Field K]
    (z : K) (hz : z ≠ 0) :
    z * (scalarVerifiedInverse z hz).inv = 1 := by
  simpa [scalarVerifiedInverse] using mul_inv_cancel₀ hz

end ConstructiveCauchyKernel
