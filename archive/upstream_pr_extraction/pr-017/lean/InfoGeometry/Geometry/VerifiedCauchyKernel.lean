/-
InfoGeometry/Geometry/VerifiedCauchyKernel.lean

The individuation of the Cauchy Kernel.
Replacing the "resolvent_law" shadow with a constructive resolvent.
-/

import InfoGeometry.Geometry.BilingualAnalyticity
import InfoGeometry.OperatorAlgebra.ConstructiveCayley

noncomputable section

namespace InfoGeometry.Geometry.VerifiedCauchyKernel

open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.OperatorAlgebra.ConstructiveCayley

/-- 
A constructively verified Cauchy Kernel.
The kernel is the resolvent R(ζ) = (ζ - Z)⁻¹.
-/
structure VerifiedKernel
    {Value : Type*} [NormedRing Value] [NormedAlgebra ℝ Value]
    (_K : Value) -- The phase axis in the algebra (parameter for future compatibility)
    (Z : Value)  -- The operator point
    (ζ : ℝ)       -- The parameter
    where
  /-- The explicit kernel element (ζ·1 - Z)⁻¹ -/
  kernelVal : Value

  /-- The kernel is a true right inverse. -/
  inv_right : (algebraMap ℝ Value ζ - Z) * kernelVal = 1

  /-- The kernel is a true left inverse. -/
  inv_left : kernelVal * (algebraMap ℝ Value ζ - Z) = 1

namespace VerifiedKernel

variable {Value : Type*} [NormedRing Value] [NormedAlgebra ℝ Value]
variable {K Z : Value} {ζ : ℝ}
variable (R : VerifiedKernel K Z ζ)

/-- The real resolvent difference `ζ • 1 - Z`. -/
def resolventDiff
    (_R : VerifiedKernel K Z ζ) : Value :=
  algebraMap ℝ Value ζ - Z

/-- The resolvent difference times the kernel is `1`. -/
theorem diff_mul_kernel :
    R.resolventDiff * R.kernelVal = 1 :=
  R.inv_right

/-- The kernel times the resolvent difference is `1`. -/
theorem kernel_mul_diff :
    R.kernelVal * R.resolventDiff = 1 :=
  R.inv_left

end VerifiedKernel

/-! ## Fixed-operator kernel families -/

/--
A verified Cauchy kernel family for one fixed operator point `Z`.

The pointwise datum `VerifiedKernel K Z ζ` proves a single inverse.  This
family packages a whole admissible real parameter domain and gives a kernel
value for each parameter.
-/
structure VerifiedKernelFamily
    {Value : Type*} [NormedRing Value] [NormedAlgebra ℝ Value]
    (_K : Value)
    (Z : Value) where

  /-- Parameters where the real resolvent is available. -/
  IsAdmissible :
    ℝ → Prop

  /-- The supplied kernel value at a parameter. -/
  kernelVal :
    ℝ → Value

  /-- Right inverse law on admissible parameters. -/
  inv_right :
    ∀ ζ,
      IsAdmissible ζ →
        (algebraMap ℝ Value ζ - Z) * kernelVal ζ = 1

  /-- Left inverse law on admissible parameters. -/
  inv_left :
    ∀ ζ,
      IsAdmissible ζ →
        kernelVal ζ * (algebraMap ℝ Value ζ - Z) = 1

namespace VerifiedKernelFamily

variable {Value : Type*} [NormedRing Value] [NormedAlgebra ℝ Value]
variable {K Z : Value}
variable (R : VerifiedKernelFamily K Z)

/-- Extract the pointwise verified kernel at an admissible parameter. -/
def kernelAt
    (ζ : ℝ)
    (hζ : R.IsAdmissible ζ) :
    VerifiedKernel K Z ζ where
  kernelVal := R.kernelVal ζ
  inv_right := R.inv_right ζ hζ
  inv_left := R.inv_left ζ hζ

/--
Convert a fixed-operator real resolvent family into the generic
noncommutative Cauchy kernel interface.

The point type is `Unit` because the operator point `Z` is fixed in this
family.
-/
def toNoncommutativeCauchyKernel :
    NoncommutativeCauchyKernel ℝ Unit Value where
  IsAdmissible := fun ζ _ => R.IsAdmissible ζ
  diff := fun ζ _ => algebraMap ℝ Value ζ - Z
  kernel := fun ζ _ => R.kernelVal ζ
  left_inverse := by
    intro ζ _ hζ
    exact R.inv_right ζ hζ
  right_inverse := by
    intro ζ _ hζ
    exact R.inv_left ζ hζ

/-- Difference times kernel is `1` on admissible parameters. -/
theorem diff_mul_kernel
    (ζ : ℝ)
    (hζ : R.IsAdmissible ζ) :
    (algebraMap ℝ Value ζ - Z) * R.kernelVal ζ = 1 :=
  R.inv_right ζ hζ

/-- Kernel times difference is `1` on admissible parameters. -/
theorem kernel_mul_diff
    (ζ : ℝ)
    (hζ : R.IsAdmissible ζ) :
    R.kernelVal ζ * (algebraMap ℝ Value ζ - Z) = 1 :=
  R.inv_left ζ hζ

end VerifiedKernelFamily

/-- 
CONSTRUCTIVE PROOF: The Cauchy Kernel satisfies the First Resolvent Identity.
This identity is the algebraic source of the kernel's analyticity.
-/
theorem resolvent_identity
    {Value : Type*} [NormedRing Value] [NormedAlgebra ℝ Value]
    {K Z : Value} {ζ₁ ζ₂ : ℝ}
    (R1 : VerifiedKernel K Z ζ₁)
    (R2 : VerifiedKernel K Z ζ₂) :
    R1.kernelVal - R2.kernelVal = (ζ₂ - ζ₁) • (R1.kernelVal * R2.kernelVal) := by
  have h_diff :
      (algebraMap ℝ Value ζ₂ - Z) - (algebraMap ℝ Value ζ₁ - Z)
        = algebraMap ℝ Value (ζ₂ - ζ₁) := by
    simp [sub_sub_sub_cancel_right, map_sub]
  calc
    R1.kernelVal - R2.kernelVal
        = R1.kernelVal * 1 - 1 * R2.kernelVal := by
            rw [mul_one, one_mul]
    _ = R1.kernelVal * ((algebraMap ℝ Value ζ₂ - Z) * R2.kernelVal)
          - (R1.kernelVal * (algebraMap ℝ Value ζ₁ - Z)) * R2.kernelVal := by
            rw [R2.inv_right, R1.inv_left]
    _ = R1.kernelVal * (algebraMap ℝ Value ζ₂ - Z) * R2.kernelVal
          - R1.kernelVal * (algebraMap ℝ Value ζ₁ - Z) * R2.kernelVal := by
            simp [mul_assoc]
    _ = R1.kernelVal * ((algebraMap ℝ Value ζ₂ - Z) - (algebraMap ℝ Value ζ₁ - Z)) * R2.kernelVal := by
            simp [mul_sub, sub_mul, mul_assoc]
    _ = (R1.kernelVal * algebraMap ℝ Value (ζ₂ - ζ₁)) * R2.kernelVal := by
            rw [h_diff]
    _ = R1.kernelVal * (algebraMap ℝ Value (ζ₂ - ζ₁) * R2.kernelVal) := by
            rw [mul_assoc]
    _ = R1.kernelVal * ((ζ₂ - ζ₁) • R2.kernelVal) := by
            rw [Algebra.smul_def]
    _ = (ζ₂ - ζ₁) • (R1.kernelVal * R2.kernelVal) := by
            rw [mul_smul_comm]

end InfoGeometry.Geometry.VerifiedCauchyKernel
