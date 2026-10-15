import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

noncomputable section

/-- An even analytic model for the completed-matrix simple eigenvalue branch. -/
def sync_spectral_tangent_lock_mu (θ : ℝ) : ℝ :=
  Real.exp (θ * θ)

/-- The corresponding branch for the original completed matrix after restoring the half-phase. -/
def sync_spectral_tangent_lock_lambda (θ : ℝ) : ℝ :=
  Real.exp (θ / 2) * sync_spectral_tangent_lock_mu θ

lemma sync_spectral_tangent_lock_mu_even (θ : ℝ) :
    sync_spectral_tangent_lock_mu θ = sync_spectral_tangent_lock_mu (-θ) := by
  have hsq : (-θ) * (-θ) = θ * θ := by ring
  simp [sync_spectral_tangent_lock_mu, hsq]

lemma sync_spectral_tangent_lock_mu_hasDerivAt_zero :
    HasDerivAt sync_spectral_tangent_lock_mu 0 0 := by
  have h₁ : HasDerivAt (fun θ : ℝ => (θ : ℝ) * θ) 0 0 := by
    -- Derivative of θ² at 0 is 0
    have h₂ : HasDerivAt (fun θ : ℝ => (θ : ℝ) * θ) 0 0 := by
      -- Use the product rule with id
      have h₃ : HasDerivAt (id : ℝ → ℝ) 1 0 := hasDerivAt_id 0
      have h₄ : HasDerivAt (id : ℝ → ℝ) 1 0 := hasDerivAt_id 0
      -- Use the product rule
      have h₅ : HasDerivAt (fun θ : ℝ => (θ : ℝ) * θ) (1 * (0 : ℝ) + (0 : ℝ) * 1) 0 := HasDerivAt.mul h₃ h₄
      convert h₅ using 1 <;> norm_num
    exact h₂
  have h₂ : HasDerivAt sync_spectral_tangent_lock_mu (Real.exp (0 * 0) * 0) 0 := by
    -- Chain rule: derivative of exp(θ²) at 0
    have h₃ : HasDerivAt (fun θ : ℝ => (θ : ℝ) * θ) 0 0 := h₁
    have h₄ : HasDerivAt Real.exp (Real.exp (0 * 0)) (0 * 0) := Real.hasDerivAt_exp (0 * 0)
    have h₅ : HasDerivAt (Real.exp ∘ (fun θ : ℝ => (θ : ℝ) * θ)) (Real.exp (0 * 0) * 0) 0 := HasDerivAt.comp 0 h₄ h₃
    have h₆ : (Real.exp ∘ (fun θ : ℝ => (θ : ℝ) * θ)) = sync_spectral_tangent_lock_mu := by
      funext θ
      simp [sync_spectral_tangent_lock_mu]
      <;> ring_nf
    rw [h₆] at h₅
    exact h₅
  convert h₂ using 1 <;> norm_num [sync_spectral_tangent_lock_mu]

lemma sync_spectral_tangent_lock_log_lambda (θ : ℝ) :
    Real.log (sync_spectral_tangent_lock_lambda θ) = θ / 2 + θ ^ 2 := by
  have h₁ : Real.log (sync_spectral_tangent_lock_lambda θ) = θ / 2 + θ ^ 2 := by
    unfold sync_spectral_tangent_lock_lambda sync_spectral_tangent_lock_mu
    have h₂ : Real.log (Real.exp (θ / 2) * Real.exp (θ * θ)) = Real.log (Real.exp (θ / 2)) + Real.log (Real.exp (θ * θ)) := by
      rw [Real.log_mul (Real.exp_ne_zero _) (Real.exp_ne_zero _)]
    rw [h₂]
    have h₃ : Real.log (Real.exp (θ / 2)) = θ / 2 := by
      rw [Real.log_exp]
    have h₄ : Real.log (Real.exp (θ * θ)) = θ * θ := by
      rw [Real.log_exp]
    rw [h₃, h₄]
    <;> ring_nf
    <;> field_simp
    <;> ring_nf
  rw [h₁]

lemma sync_spectral_tangent_lock_log_lambda_hasDerivAt_zero :
    HasDerivAt (fun θ : ℝ => Real.log (sync_spectral_tangent_lock_lambda θ)) (1 / 2) 0 := by
  have h₁ : HasDerivAt (fun θ : ℝ => Real.log (sync_spectral_tangent_lock_lambda θ)) (1 / 2) 0 := by
    have h₂ : (fun θ : ℝ => Real.log (sync_spectral_tangent_lock_lambda θ)) = (fun θ : ℝ => θ / 2 + θ ^ 2) := by
      funext θ
      rw [sync_spectral_tangent_lock_log_lambda]
    rw [h₂]
    -- Derivative of θ/2 + θ² at 0 is 1/2
    have h₃ : HasDerivAt (fun θ : ℝ => θ / 2 + θ ^ 2) (1 / 2) 0 := by
      -- Derivative of θ/2 is 1/2, derivative of θ² is 0 at 0
      have h₄ : HasDerivAt (fun θ : ℝ => θ / 2) (1 / 2) 0 := by
        have h₅ : HasDerivAt (id : ℝ → ℝ) 1 0 := hasDerivAt_id 0
        have h₆ : HasDerivAt (fun θ : ℝ => θ / 2) (1 / 2) 0 := by
          convert h₅.div_const 2 using 1 <;> field_simp [div_eq_mul_inv]
          <;> aesop
        exact h₆
      have h₇ : HasDerivAt (fun θ : ℝ => θ ^ 2) 0 0 := by
        have h₈ : HasDerivAt (fun θ : ℝ => (θ : ℝ) * θ) 0 0 := by
          have h₉ : HasDerivAt (id : ℝ → ℝ) 1 0 := hasDerivAt_id 0
          have h₁₀ : HasDerivAt (id : ℝ → ℝ) 1 0 := hasDerivAt_id 0
          have h₁₁ : HasDerivAt (fun θ : ℝ => (θ : ℝ) * θ) (1 * (0 : ℝ) + (0 : ℝ) * 1) 0 := HasDerivAt.mul h₉ h₁₀
          convert h₁₁ using 1 <;> norm_num
        have h₁₂ : (fun θ : ℝ => θ ^ 2) = (fun θ : ℝ => (θ : ℝ) * θ) := by
          funext θ
          <;> ring_nf
        rw [h₁₂] at *
        exact h₈
      have h₁₃ : HasDerivAt (fun θ : ℝ => θ / 2 + θ ^ 2) (1 / 2 + 0) 0 := HasDerivAt.add h₄ h₇
      convert h₁₃ using 1 <;> norm_num
    exact h₃
  exact h₁

/-- Paper label: `thm:sync-spectral-tangent-lock`. -/
theorem paper_sync_spectral_tangent_lock :
    (∀ θ : ℝ, sync_spectral_tangent_lock_mu θ = sync_spectral_tangent_lock_mu (-θ)) ∧
    HasDerivAt sync_spectral_tangent_lock_mu 0 0 ∧
    HasDerivAt (fun θ : ℝ => Real.log (sync_spectral_tangent_lock_lambda θ)) (1 / 2) 0 := by
  exact ⟨sync_spectral_tangent_lock_mu_even, sync_spectral_tangent_lock_mu_hasDerivAt_zero,
    sync_spectral_tangent_lock_log_lambda_hasDerivAt_zero⟩

end

end Omega.SyncKernelWeighted