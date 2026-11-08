import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.Ring

notation:max x "⁻²" => x⁻¹^2

theorem central_charge_b (b : ℝ) (hb : b ≠ 0) : 1 + 6 * (b + b⁻¹)^2 = 13 + 6 * b^2 + 6 * b⁻² := by
  have h : b * b⁻¹ = 1 := mul_inv_cancel₀ hb
  calc 1 + 6 * (b + b⁻¹)^2
    _ = 1 + 6 * b^2 + 12 * (b * b⁻¹) + 6 * b⁻² := by ring
    _ = 1 + 6 * b^2 + 12 * 1 + 6 * b⁻² := by rw [h]
    _ = 13 + 6 * b^2 + 6 * b⁻² := by ring
