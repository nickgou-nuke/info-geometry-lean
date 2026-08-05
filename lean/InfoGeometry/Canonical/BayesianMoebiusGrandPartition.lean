import Mathlib
import InfoGeometry.Canonical.BayesianMoebius

namespace InfoGeometry.Canonical

open Real

/-- Grand-canonical site responsibility function. -/
noncomputable def siteResponsibility (q b : ℝ) : ℝ :=
  (q * b) / (1 + q * b)

theorem bayesUpdate_eq_siteResponsibility {α b : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hb : 0 < b) :
    bayesUpdate b α = siteResponsibility (α / (1 - α)) b := by
  dsimp [bayesUpdate, siteResponsibility]
  have hp : 1 - α > 0 := sub_pos.mpr hα1
  have h_mul : ((α / (1 - α)) * b) = (α * b) / (1 - α) := by ring
  rw [h_mul]
  have h_den : 1 + (α * b) / (1 - α) = (1 - α + α * b) / (1 - α) := by
    have h_eq : (1 : ℝ) = (1 - α) / (1 - α) := (div_self (ne_of_gt hp)).symm
    nth_rw 1 [h_eq]
    rw [← add_div]
  rw [h_den]
  have h_den_b : 1 + (b - 1) * α = 1 - α + α * b := by ring
  rw [h_den_b]
  have h_div_div : ((α * b) / (1 - α)) / ((1 - α + α * b) / (1 - α)) = (α * b) / (1 - α + α * b) := by
    exact div_div_div_cancel_right₀ (ne_of_gt hp) (α * b) (1 - α + α * b)
  rw [h_div_div]
  congr 1
  ring

theorem bayesUpdate_eq_evidenceGapEncode {α d ε μ_c : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hε : 0 < ε)
    (h_μ_c : ε * logit α = μ_c) :
    bayesUpdate (Real.exp (-(d / ε))) α = evidenceGapEncode (μ_c - d) ε := by
  -- bayesUpdate b α = sigmoid (logit α + log b)
  have hb : 0 < Real.exp (-(d / ε)) := Real.exp_pos _
  have h_flow := bayesFlow_eq_sigmoid (-(d / ε)) α hα0 hα1
  have h_log : Real.log (Real.exp (-(d / ε))) = -(d / ε) := Real.log_exp _
  dsimp [evidenceGapEncode]
  -- We know evidenceGapEncode N ε = 1 / (1 + exp (-N/ε)) = sigmoid (N / ε)
  -- Here N = μ_c - d. N / ε = (ε * logit α - d) / ε = logit α - d / ε
  have h_gap : (μ_c - d) / ε = logit α - d / ε := by
    rw [← h_μ_c, sub_div]
    have h_cancel : (ε * logit α) / ε = logit α := by
      exact mul_div_cancel_left₀ (logit α) (ne_of_gt hε)
    rw [h_cancel]
  have h_RHS : 1 / (1 + Real.exp (-((μ_c - d) / ε))) = sigmoid ((μ_c - d) / ε) := rfl
  rw [h_RHS, h_gap]
  have h_flow2 : bayesUpdate (Real.exp (-(d / ε))) α = bayesFlow (-(d / ε)) α := rfl
  rw [h_flow2, h_flow]
  congr 1

theorem recursive_estimator_substitution {ρ S_prev N_prev X B_prev α d_t ε r : ℝ}
    (hB : B_prev = S_prev / N_prev)
    (hN_prev : N_prev ≠ 0)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hr : r = bayesUpdate (Real.exp (-(d_t / ε))) α)
    (hN : ρ * N_prev + r ≠ 0) :
    updateBackground (updateSum ρ S_prev r X) (updateMass ρ N_prev r) =
      B_prev + (r / (ρ * N_prev + r)) * (X - B_prev) := by
  rw [barycentric_update ρ S_prev N_prev r X B_prev hB hN hN_prev]

end InfoGeometry.Canonical
