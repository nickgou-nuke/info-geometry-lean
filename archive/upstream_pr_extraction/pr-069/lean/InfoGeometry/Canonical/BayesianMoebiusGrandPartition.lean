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

theorem bayesUpdate_eq_evidenceGapEncode_native {α d ε μ_c : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hε : 0 < ε)
    (h_μ_c : ε * logit α = μ_c) :
    bayesUpdate (Real.exp (-(d / ε))) α = evidenceGapEncode (μ_c - d) ε := by
  dsimp [bayesUpdate, evidenceGapEncode, logit] at *
  have h_logit : Real.log (α / (1 - α)) = μ_c / ε := by
    rw [← h_μ_c, mul_div_cancel_left₀ (Real.log (α / (1 - α))) (ne_of_gt hε)]
  have h_exp_logit : Real.exp (Real.log (α / (1 - α))) = Real.exp (μ_c / ε) := by rw [h_logit]
  have h_frac_pos : 0 < α / (1 - α) := div_pos hα0 (sub_pos.mpr hα1)
  rw [Real.exp_log h_frac_pos] at h_exp_logit
  have h_alpha1 : α = Real.exp (μ_c / ε) / (1 + Real.exp (μ_c / ε)) := by
    have h_div := (div_eq_iff (ne_of_gt (sub_pos.mpr hα1))).mp h_exp_logit
    have h_div_symm : α = (1 - α) * Real.exp (μ_c / ε) := by rw [mul_comm]; exact h_div
    have h_add : α * (1 + Real.exp (μ_c / ε)) = Real.exp (μ_c / ε) := by
      calc α * (1 + Real.exp (μ_c / ε))
        _ = α + α * Real.exp (μ_c / ε) := by rw [mul_add, mul_one]
        _ = (1 - α) * Real.exp (μ_c / ε) + α * Real.exp (μ_c / ε) := by rw [← h_div_symm]
        _ = (1 - α + α) * Real.exp (μ_c / ε) := by rw [add_mul]
        _ = 1 * Real.exp (μ_c / ε) := by ring_nf
        _ = Real.exp (μ_c / ε) := one_mul _
    have h3 : 1 + Real.exp (μ_c / ε) ≠ 0 := ne_of_gt (add_pos zero_lt_one (Real.exp_pos _))
    exact (eq_div_iff h3).mpr h_add
  
  let E := Real.exp (-(d / ε))
  let M := Real.exp (μ_c / ε)
  have hd1 : α = M / (1 + M) := h_alpha1
  have h_num : E * α = (E * M) / (1 + M) := by rw [hd1, mul_div_assoc]
  have h_den : 1 + (E - 1) * α = (1 + E * M) / (1 + M) := by
    rw [hd1]
    have h5 : 1 + M ≠ 0 := ne_of_gt (add_pos zero_lt_one (Real.exp_pos _))
    have h6 : (1 : ℝ) = (1 + M) / (1 + M) := (div_self h5).symm
    nth_rw 1 [h6]
    rw [← mul_div_assoc]
    rw [← add_div]
    congr 1
    ring
  have h_bayes : (E * α) / (1 + (E - 1) * α) = (E * M) / (1 + E * M) := by
    rw [h_num, h_den]
    have h5 : 1 + M ≠ 0 := ne_of_gt (add_pos zero_lt_one (Real.exp_pos _))
    exact div_div_div_cancel_right₀ h5 (E * M) (1 + E * M)
  
  have h_EM : E * M = Real.exp ((μ_c - d) / ε) := by
    dsimp [E, M]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h_bayes, h_EM]
  
  have h_target_eq : (Real.exp ((μ_c - d) / ε)) / (1 + Real.exp ((μ_c - d) / ε)) = 1 / (1 + Real.exp (-((μ_c - d) / ε))) := by
    have h_inv : Real.exp (-((μ_c - d) / ε)) = (Real.exp ((μ_c - d) / ε))⁻¹ := Real.exp_neg _
    rw [h_inv, inv_eq_one_div]
    have hK : Real.exp ((μ_c - d) / ε) ≠ 0 := ne_of_gt (Real.exp_pos _)
    have h_denom : 1 + 1 / Real.exp ((μ_c - d) / ε) = (Real.exp ((μ_c - d) / ε) + 1) / Real.exp ((μ_c - d) / ε) := by
      have h1 : (1 : ℝ) = Real.exp ((μ_c - d) / ε) / Real.exp ((μ_c - d) / ε) := (div_self hK).symm
      nth_rw 1 [h1]
      rw [← add_div]
    rw [h_denom, one_div]
    have h_add_comm : Real.exp ((μ_c - d) / ε) + 1 = 1 + Real.exp ((μ_c - d) / ε) := add_comm _ _
    rw [h_add_comm]
    rw [inv_div]
  exact h_target_eq

theorem recursive_estimator_substitution {ρ S_prev N_prev X B_prev α d_t ε r : ℝ}
    (hB : B_prev = S_prev / N_prev)
    (hN_prev : N_prev ≠ 0)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hr : r = bayesUpdate (Real.exp (-(d_t / ε))) α)
    (hN : ρ * N_prev + r ≠ 0) :
    updateBackground (updateSum ρ S_prev r X) (updateMass ρ N_prev r) =
      B_prev + (r / (ρ * N_prev + r)) * (X - B_prev) := by
  dsimp [updateBackground, updateSum, updateMass]
  rw [hB]
  have h1 : ρ * N_prev + r ≠ 0 := hN
  have h2 : N_prev ≠ 0 := hN_prev
  
  apply mul_left_cancel₀ h1
  rw [mul_div_cancel₀ _ h1]
  
  rw [mul_add]
  have h_right_second : (ρ * N_prev + r) * (r / (ρ * N_prev + r) * (X - S_prev / N_prev)) = r * (X - S_prev / N_prev) := by
    rw [← mul_assoc, mul_div_cancel₀ _ h1]
  rw [h_right_second]
  
  have h_right_first : (ρ * N_prev + r) * (S_prev / N_prev) = ρ * S_prev + r * (S_prev / N_prev) := by
    rw [add_mul]
    have h_term_sub : ρ * N_prev * (S_prev / N_prev) = ρ * S_prev := by
      rw [mul_assoc, mul_div_cancel₀ _ h2]
    rw [h_term_sub]
  rw [h_right_first]
  
  ring

end InfoGeometry.Canonical
