import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace InfoGeometry.Canonical

open Real

/-- The affine Poisson-Gaussian mixed deviance (c₂ = 0). -/
noncomputable def D_affine (c_1 c_0 x μ : ℝ) : ℝ :=
  (2 / c_1^2) * ((c_1 * x + c_0) * log ((c_1 * x + c_0) / (c_1 * μ + c_0)) - c_1 * (x - μ))

/-- The pure Gamma deviance (c₀ = c₁ = 0). -/
noncomputable def D_gamma_mix (c_2 x μ : ℝ) : ℝ :=
  (2 / c_2) * ((x / μ) - log (x / μ) - 1)

/-- The effective power exponent p_eff(μ) = μ * V'(μ) / V(μ).
For V(μ) = c₀ + c₁ μ + c₂ μ², V'(μ) = c₁ + 2 c₂ μ. -/
noncomputable def p_eff_mix (c_0 c_1 c_2 μ : ℝ) : ℝ :=
  (c_1 * μ + 2 * c_2 * μ^2) / (c_0 + c_1 * μ + c_2 * μ^2)

/-- The effective beta β_eff(μ) = 2 - p_eff(μ). -/
noncomputable def beta_eff_mix (c_0 c_1 c_2 μ : ℝ) : ℝ :=
  2 - p_eff_mix c_0 c_1 c_2 μ

/-- Theorem: beta_eff_mix simplifies to (2c₀ + c₁μ) / (c₀ + c₁μ + c₂μ²). -/
theorem beta_eff_mix_eq (c_0 c_1 c_2 μ : ℝ) (hV : c_0 + c_1 * μ + c_2 * μ^2 ≠ 0) :
    beta_eff_mix c_0 c_1 c_2 μ = (2 * c_0 + c_1 * μ) / (c_0 + c_1 * μ + c_2 * μ^2) := by
  dsimp [beta_eff_mix, p_eff_mix]
  have h_eq : (2 : ℝ) - (c_1 * μ + 2 * c_2 * μ^2) / (c_0 + c_1 * μ + c_2 * μ^2) =
    (2 * (c_0 + c_1 * μ + c_2 * μ^2) - (c_1 * μ + 2 * c_2 * μ^2)) / (c_0 + c_1 * μ + c_2 * μ^2) := by
    rw [sub_eq_iff_eq_add]
    have h_add : (2 * (c_0 + c_1 * μ + c_2 * μ^2) - (c_1 * μ + 2 * c_2 * μ^2)) / (c_0 + c_1 * μ + c_2 * μ^2) + (c_1 * μ + 2 * c_2 * μ^2) / (c_0 + c_1 * μ + c_2 * μ^2) = (2 * (c_0 + c_1 * μ + c_2 * μ^2)) / (c_0 + c_1 * μ + c_2 * μ^2) := by
      rw [← add_div, sub_add_cancel]
    rw [h_add, mul_div_cancel_right₀ _ hV]
  rw [h_eq]
  congr 1
  ring

end InfoGeometry.Canonical
