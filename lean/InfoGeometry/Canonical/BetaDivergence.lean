import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace InfoGeometry.Canonical

open Real

/-- The Gaussian beta=2 deviance -/
noncomputable def d_2 (x μ : ℝ) : ℝ :=
  (1 / 2) * (x - μ)^2

/-- The Poisson beta=1 deviance -/
noncomputable def d_1 (x μ : ℝ) : ℝ :=
  x * log (x / μ) - x + μ

/-- The Gamma beta=0 deviance -/
noncomputable def d_0 (x μ : ℝ) : ℝ :=
  (x / μ) - log (x / μ) - 1

/-- Generating potential for beta=2 -/
noncomputable def phi_2 (μ : ℝ) : ℝ :=
  μ^2 / 2

/-- Generating potential for beta=1 -/
noncomputable def phi_1 (μ : ℝ) : ℝ :=
  μ * log μ - μ

/-- Generating potential for beta=0 -/
noncomputable def phi_0 (μ : ℝ) : ℝ :=
  - log μ

/-- Generating potential for general beta ≠ 0, 1 -/
noncomputable def phi_beta (β μ : ℝ) : ℝ :=
  μ^β / (β * (β - 1))

/-- The general beta deviance -/
noncomputable def d_beta (β x μ : ℝ) : ℝ :=
  (x^β + (β - 1) * μ^β - β * x * μ^(β - 1)) / (β * (β - 1))

/-- Theorem: d_beta is the Bregman divergence of phi_beta -/
theorem d_beta_is_bregman (β x μ : ℝ) (h0 : β ≠ 0) (h1 : β ≠ 1) (hx : 0 < x) (hμ : 0 < μ) :
    d_beta β x μ = phi_beta β x - phi_beta β μ - (μ^(β - 1) / (β - 1)) * (x - μ) := by
  have h_mul : μ^(β - 1) * μ = μ^β := by
    calc
      μ^(β - 1) * μ = μ^(β - 1) * μ^(1:ℝ) := by rw [Real.rpow_one]
      _ = μ^(β - 1 + 1) := by rw [← Real.rpow_add hμ]
      _ = μ^β := by congr 1; ring
  have h_beta_sub_one : β - 1 ≠ 0 := sub_ne_zero.mpr h1
  dsimp [d_beta, phi_beta]
  have h_den : β * (β - 1) ≠ 0 := mul_ne_zero h0 h_beta_sub_one
  apply mul_right_cancel₀ h_den
  calc
    ((x ^ β + (β - 1) * μ ^ β - β * x * μ ^ (β - 1)) / (β * (β - 1))) * (β * (β - 1))
      = x ^ β + (β - 1) * μ ^ β - β * x * μ ^ (β - 1) := by rw [div_mul_cancel₀ _ h_den]
    _ = x ^ β - μ ^ β - β * x * μ ^ (β - 1) + β * μ ^ β := by ring
    _ = x ^ β - μ ^ β - β * x * μ ^ (β - 1) + β * (μ ^ (β - 1) * μ) := by rw [h_mul]
    _ = (x ^ β / (β * (β - 1)) - μ ^ β / (β * (β - 1)) - μ ^ (β - 1) / (β - 1) * (x - μ)) * (β * (β - 1)) := by
      symm
      calc
        (x ^ β / (β * (β - 1)) - μ ^ β / (β * (β - 1)) - μ ^ (β - 1) / (β - 1) * (x - μ)) * (β * (β - 1))
          = (x ^ β / (β * (β - 1))) * (β * (β - 1)) - (μ ^ β / (β * (β - 1))) * (β * (β - 1)) - (μ ^ (β - 1) / (β - 1) * (x - μ)) * (β * (β - 1)) := by
            rw [sub_mul, sub_mul]
        _ = x ^ β - μ ^ β - (μ ^ (β - 1) / (β - 1) * (x - μ)) * (β * (β - 1)) := by
            rw [div_mul_cancel₀ _ h_den, div_mul_cancel₀ _ h_den]
        _ = x ^ β - μ ^ β - β * x * μ ^ (β - 1) + β * (μ ^ (β - 1) * μ) := by
          have h_term : (μ ^ (β - 1) / (β - 1) * (x - μ)) * (β * (β - 1)) = β * x * μ ^ (β - 1) - β * (μ ^ (β - 1) * μ) := by
            calc
              (μ ^ (β - 1) / (β - 1) * (x - μ)) * (β * (β - 1))
                = (μ ^ (β - 1) / (β - 1)) * (β - 1) * β * (x - μ) := by ring
              _ = μ ^ (β - 1) * β * (x - μ) := by rw [div_mul_cancel₀ _ h_beta_sub_one]
              _ = β * x * μ ^ (β - 1) - β * (μ ^ (β - 1) * μ) := by ring
          rw [h_term]
          ring

/-- Theorem: d_2 is the Bregman divergence of phi_2 -/
theorem d_2_is_bregman (x μ : ℝ) :
    d_2 x μ = phi_2 x - phi_2 μ - μ * (x - μ) := by
  dsimp [d_2, phi_2]
  ring

/-- Theorem: d_1 is the Bregman divergence of phi_1 -/
theorem d_1_is_bregman (x μ : ℝ) (hx : 0 < x) (hμ : 0 < μ) :
    d_1 x μ = phi_1 x - phi_1 μ - (log μ) * (x - μ) := by
  dsimp [d_1, phi_1]
  have h_log_div : log (x / μ) = log x - log μ := log_div hx.ne' hμ.ne'
  rw [h_log_div]
  ring

/-- Theorem: d_0 is the Bregman divergence of phi_0 -/
theorem d_0_is_bregman (x μ : ℝ) (hx : 0 < x) (hμ : 0 < μ) :
    d_0 x μ = phi_0 x - phi_0 μ - (- (1 / μ)) * (x - μ) := by
  dsimp [d_0, phi_0]
  have h_log_div : log (x / μ) = log x - log μ := log_div hx.ne' hμ.ne'
  have h_mul_inv : μ * (1 / μ) = 1 := by exact mul_one_div_cancel hμ.ne'
  rw [h_log_div]
  calc
    (x / μ) - (log x - log μ) - 1 = x * (1 / μ) - log x + log μ - 1 := by ring
    _ = - log x + log μ - μ * (1 / μ) + x * (1 / μ) := by rw [h_mul_inv]; ring
    _ = - log x - (- log μ) - (- (1 / μ)) * (x - μ) := by ring

end InfoGeometry.Canonical
