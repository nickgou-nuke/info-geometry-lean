/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TwoSidedCayleyDicksonLaplaceKernel
import InfoGeometry.Capstone.GrandIdentityDeRhamModular

/-!
# Gap 3: Two-Sided Laplace Kernel = KMS / Modular Flow (scalar specialization)

Connects the two-sided hyperbolic Laplace kernel to scalar modular thermodynamics.
-/

namespace InfoGeometry.Canonical.TwoSidedLaplaceModularFlowBridge

open InfoGeometry.Canonical
open InfoGeometry.Core.DualSeedPeirce
open InfoGeometry.Core.DualSeedPeirce.IsDualSeedPair
open InfoGeometry.Canonical.TwoSidedCayleyDicksonLaplaceKernel

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-!
### Scalar modular flow identification
-/

/-- The hyperbolic kernel with exponential parameters is `exp(-στ) • P_+ + exp(στ) • P_-`. -/
theorem laplace_modular_flow_scalar {d B : A} (_ : IsDualSeedPair d B) {σ τ : ℝ} :
    hyperbolicKernel (Real.exp (-σ * τ)) (Real.exp (σ * τ)) d B =
      Real.exp (-σ * τ) • polePlus d B + Real.exp (σ * τ) • poleMinus d B := by
  rfl

/-!
### KMS unimodularity: antisymmetric Laplace fixes the poles
-/

/-- When `λ * μ = 1`, the antisymmetric two-sided Laplace fixes both poles. -/
theorem laplace_kms_unimodularity {d B : A} (h : IsDualSeedPair d B) {lam mu : ℝ} (h_lm : lam * mu = 1) :
    twoSidedHyperbolicLaplace lam mu mu lam d B (polePlus d B) = polePlus d B ∧
    twoSidedHyperbolicLaplace lam mu mu lam d B (poleMinus d B) = poleMinus d B := by
  have h_sel := symmetric_vs_antisymmetric_laplace_selectivity h h_lm
  exact ⟨h_sel.2.1, h_sel.2.2.1⟩

/-- The antisymmetric Laplace with exponential parameters is constantly `polePlus`. -/
theorem laplace_modular_flow_const_polePlus {d B : A} (h : IsDualSeedPair d B) (t : ℝ) :
    twoSidedHyperbolicLaplace (Real.exp (-t)) (Real.exp t) (Real.exp t) (Real.exp (-t)) d B (polePlus d B) =
      polePlus d B := by
  have h_lm : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]
    simp
  exact (laplace_kms_unimodularity h h_lm).1

/-- Derivative of the symmetric two-sided Laplace with exponential parameters at 0 is 0. -/
theorem laplace_derivative_first_law {d B : ℝ} (h : IsDualSeedPair d B) :
    deriv (fun t : ℝ => twoSidedHyperbolicLaplace (Real.exp (-t)) (Real.exp t)
      (Real.exp t) (Real.exp (-t)) d B (polePlus d B)) 0 = 0 := by
  have h₁ : (fun t : ℝ => twoSidedHyperbolicLaplace (Real.exp (-t)) (Real.exp t)
      (Real.exp t) (Real.exp (-t)) d B (polePlus d B)) = (fun t : ℝ => (polePlus d B : ℝ)) := by
    funext t
    have h₂ := twoSidedHyperbolicLaplace_sector_scaling h (Real.exp (-t)) (Real.exp t) (Real.exp t) (Real.exp (-t))
    have h₃ := h₂.1
    have h₄ : (Real.exp (-t) : ℝ) * Real.exp t = 1 := by
      rw [← Real.exp_add]
      ring_nf
      <;> simp [Real.exp_neg]
      <;> field_simp
    calc
      twoSidedHyperbolicLaplace (Real.exp (-t)) (Real.exp t) (Real.exp t) (Real.exp (-t)) d B (polePlus d B)
        = ((Real.exp (-t) : ℝ) * Real.exp t) • polePlus d B := by
          simpa [mul_assoc, mul_comm, mul_left_comm] using h₃
      _ = (1 : ℝ) • polePlus d B := by rw [h₄]
      _ = (polePlus d B : ℝ) := by simp [one_smul]
  rw [h₁]
  simp [deriv_const]

end InfoGeometry.Canonical.TwoSidedLaplaceModularFlowBridge
