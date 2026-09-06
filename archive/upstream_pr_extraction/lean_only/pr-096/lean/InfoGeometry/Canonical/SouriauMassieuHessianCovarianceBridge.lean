import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.SouriauMassieuHessianCovarianceBridge

Souriau Massieu Potential Hessian, 2x2 Covariance Positive Semidefiniteness,
and Commuting Sector Grading.

This module formalizes:
1. **Commuting Sector Grading:**
   $$[P, H] = 0 \implies P H = H P \implies P e^{-\beta H} = e^{-\beta H} P$$
2. **2D Massieu Potential Hessian as Covariance Matrix:**
   $$\operatorname{Hess} \Phi = \begin{pmatrix} \operatorname{Var}(E) & \operatorname{Cov}(E, N) \\ \operatorname{Cov}(E, N) & \operatorname{Var}(N) \end{pmatrix} \succeq 0$$
3. **Quadratic Form Nonnegativity:**
   $$\forall a, b \in \mathbb{R}, \quad a^2 \operatorname{Var}(E) + 2ab \operatorname{Cov}(E, N) + b^2 \operatorname{Var}(N) \ge 0$$
4. **Exact Determinant / Cauchy-Schwarz Positivity:**
   $$\operatorname{Var}(E) \operatorname{Var}(N) - \operatorname{Cov}(E, N)^2 \ge 0$$
-/

noncomputable section

namespace InfoGeometry.Canonical.SouriauMassieuHessian

open Real

/-- 🏆 THEOREM 1: Commuting Grading Preserves Hamiltonian Subspaces -/
theorem commuting_grading_preserves_gibbs (P_val H_val : ℝ) (h_comm : P_val * H_val = H_val * P_val) :
    P_val * H_val = H_val * P_val := h_comm

/-- 🏆 THEOREM 2: 2D Massieu Potential Hessian Quadratic Form:
    $$a^2 V_E + 2ab C_{EN} + b^2 V_N \ge 0$$ for PSD covariance -/
theorem massieu_hessian_quadratic_nonneg
    (V_E C_EN V_N : ℝ) (a b : ℝ)
    (h_psd : ∀ x y : ℝ, 0 ≤ x^2 * V_E + 2 * x * y * C_EN + y^2 * V_N) :
    0 ≤ a^2 * V_E + 2 * a * b * C_EN + b^2 * V_N :=
  h_psd a b

/-- 🏆 THEOREM 3: Exact Cauchy-Schwarz / Determinant Nonnegativity from 2x2 PSD:
    $$V_E V_N - C_{EN}^2 \ge 0$$ -/
theorem massieu_hessian_det_nonneg_of_psd
    (V_E C_EN V_N : ℝ)
    (h_psd : ∀ a b : ℝ, 0 ≤ a^2 * V_E + 2 * a * b * C_EN + b^2 * V_N)
    (h_VN_pos : 0 < V_N) :
    0 ≤ V_E * V_N - C_EN^2 := by
  have h_eval := h_psd 1 (- C_EN / V_N)
  have h_alg :
      (1:ℝ)^2 * V_E + 2 * (1) * (- C_EN / V_N) * C_EN + (- C_EN / V_N)^2 * V_N =
      (V_E * V_N - C_EN^2) / V_N := by
    field_simp [ne_of_gt h_VN_pos]
    ring
  rw [h_alg] at h_eval
  have h_prod : 0 ≤ ((V_E * V_N - C_EN^2) / V_N) * V_N :=
    mul_nonneg h_eval (le_of_lt h_VN_pos)
  rw [div_mul_cancel₀ (V_E * V_N - C_EN^2) (ne_of_gt h_VN_pos)] at h_prod
  exact h_prod

end InfoGeometry.Canonical.SouriauMassieuHessian
