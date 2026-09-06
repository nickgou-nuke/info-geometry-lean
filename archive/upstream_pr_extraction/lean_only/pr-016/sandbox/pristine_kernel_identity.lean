import Mathlib
import InfoGeometry.Geometry.BilingualAnalyticity

/-!
# Sandbox: Pristine Cauchy Kernel Individuation
Constructive proof of the Resolvent Identity without 'sorry'.
Using explicit algebraic steps with mul_sub and sub_mul.
Fixing rewrite syntax and tactic order.
-/

noncomputable section

namespace InfoGeometry.Geometry.VerifiedCauchyKernel.Sandbox

/-- 
A constructively verified Cauchy Kernel.
The kernel is the resolvent R(ζ) = (ζ - Z)⁻¹.
-/
structure VerifiedKernel
    {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value] [Ring Value] [Algebra ℝ Value]
    (_K : Value) -- The phase axis
    (Z : Value)  -- The operator point
    (ζ : ℝ)       -- The parameter
    where
  kernelVal : Value
  inv_right : (algebraMap ℝ Value ζ - Z) * kernelVal = 1
  inv_left : kernelVal * (algebraMap ℝ Value ζ - Z) = 1

/-- 
PRISTINE CONSTRUCTIVE THEOREM: The First Resolvent Identity.
Eliminating the 'sorry' from the main repository.
-/
theorem resolvent_identity_pristine
    {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value] [Ring Value] [Algebra ℝ Value]
    {K Z : Value} {ζ₁ ζ₂ : ℝ}
    (R1 : VerifiedKernel K Z ζ₁)
    (R2 : VerifiedKernel K Z ζ₂) :
    R1.kernelVal - R2.kernelVal = (ζ₂ - ζ₁) • (R1.kernelVal * R2.kernelVal) := by
  let A1 := algebraMap ℝ Value ζ₁ - Z
  let A2 := algebraMap ℝ Value ζ₂ - Z
  
  -- Evaluate the difference of the denominators A2 - A1
  have h_diff : A2 - A1 = algebraMap ℝ Value (ζ₂ - ζ₁) := by
    unfold_let A1 A2
    rw [sub_sub_sub_cancel_right]
    exact (map_sub (algebraMap ℝ Value) ζ₂ ζ₁).symm

  -- Prove R1 - R2 = R1 * (A2 - A1) * R2
  have h_mid : R1.kernelVal - R2.kernelVal = R1.kernelVal * (A2 - A1) * R2.kernelVal := by
    calc
      R1.kernelVal - R2.kernelVal 
        = R1.kernelVal * 1 - 1 * R2.kernelVal := by rw [mul_one, one_mul]
      _ = R1.kernelVal * (A2 * R2.kernelVal) - (R1.kernelVal * A1) * R2.kernelVal := by 
          rw [R2.inv_right, R1.inv_left]
          simp only [A1, A2]
      _ = R1.kernelVal * A2 * R2.kernelVal - R1.kernelVal * A1 * R2.kernelVal := by 
          rw [mul_assoc, mul_assoc]
      _ = (R1.kernelVal * A2 - R1.kernelVal * A1) * R2.kernelVal := by rw [sub_mul]
      _ = R1.kernelVal * (A2 - A1) * R2.kernelVal := by rw [mul_sub]

  -- Combine
  rw [h_mid, h_diff]
  
  -- algebraMap (ζ₂ - ζ₁) * R2 = (ζ₂ - ζ₁) • R2
  have h_smul : (algebraMap ℝ Value (ζ₂ - ζ₁)) * R2.kernelVal = (ζ₂ - ζ₁) • R2.kernelVal := by
    exact Algebra.algebraMap_mul_comm (ζ₂ - ζ₁) R2.kernelVal
    
  rw [mul_assoc, h_smul, smul_mul_assoc]

end InfoGeometry.Geometry.VerifiedCauchyKernel.Sandbox
