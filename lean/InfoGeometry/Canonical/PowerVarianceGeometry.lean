import Mathlib.Analysis.Calculus.Deriv.Pow
import InfoGeometry.Canonical.BetaDivergence

namespace InfoGeometry.Canonical

open Real

/-- The algebraic second derivative of phi_beta is μ^(β - 2). -/
noncomputable def phi_beta_deriv2 (β μ : ℝ) : ℝ := μ^(β - 2)

/-- The power-variance exponent p = 2 - β. -/
def p_eff (β : ℝ) : ℝ := 2 - β

/-- The variance function V_beta(μ) = φ * μ^(2 - β). -/
noncomputable def V_beta (φ β μ : ℝ) : ℝ :=
  φ * μ^(2 - β)

/-- Theorem: V_beta is proportional to the reciprocal of phi_beta''. -/
theorem V_beta_eq_recip_deriv2 (φ β μ : ℝ) (h0 : β ≠ 0) (h1 : β ≠ 1) (hμ : 0 < μ) :
    V_beta φ β μ = φ / (phi_beta_deriv2 β μ) := by
  dsimp [phi_beta_deriv2]
  dsimp [V_beta]
  rw [div_eq_mul_inv]
  have h_pow : (μ ^ (β - 2))⁻¹ = μ ^ (-(β - 2)) := Real.rpow_neg hμ.le _ |>.symm
  rw [h_pow]
  congr 1
  ring

end InfoGeometry.Canonical
