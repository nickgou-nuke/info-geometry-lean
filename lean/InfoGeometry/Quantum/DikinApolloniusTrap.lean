/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InfoGeometry.Quantum.DikinApolloniusTrap

open Real

noncomputable section

/-!
# Dikin Ellipsoid Information Barrier & Blahut-Arimoto Contraction on Scale Space

This module formalizes the information-theoretic Lyapunov trap mechanism:
1. **Convex Log-Barrier Potential**:
   $$\Phi(\xi) = -\ln(1 - \tanh^2(\xi)) = -\ln(1 - Q^2) = 2\ln\cosh(\xi)$$
2. **Dikin / Fisher Metric on Scale Space**:
   $$g(\xi) = \frac{d^2\Phi}{d\xi^2} = 2(1 - \tanh^2(\xi)) = \frac{2}{\cosh^2(\xi)}$$
   with strict metric positivity $g(\xi) > 0$ and equilibrium normalization $g(0) = 2$.
3. **Dikin Equilibrium Ellipsoid**:
   $$\mathcal{E}(0, r) = \{ y \in \mathbb{R} \mid g(0) \cdot y^2 \le r^2 \} = \{ y \in \mathbb{R} \mid 2 y^2 \le r^2 \}$$
4. **Blahut-Arimoto Contraction Step**:
   An operator $\mathcal{T}_{\mathrm{BA}}$ with contraction factor $K_c \in [0, 1)$ strictly contracts
   the state into a nested Dikin ellipsoid:
   $$2 (\mathcal{T}_{\mathrm{BA}}(y))^2 \le (K_c \cdot r)^2$$
-/

/-- Convex transformed information potential on the scale coordinate ξ.
It is not globally standard self-concordant in this nonlinear coordinate:
see `BinaryBarrierCoordinateHessian.transformed_barrier_self_concordance_counterexample`.
    Φ(ξ) = - ln(1 - tanh²(ξ)) = 2 ln(cosh(ξ)). -/
def dikinScaleBarrier (ξ : ℝ) : ℝ :=
  - Real.log (1 - (Real.tanh ξ) ^ 2)

/-- Dikin/Fisher information metric along the scale space:
    g(ξ) = 2 (1 - tanh²(ξ)) = 2 / cosh²(ξ). -/
def dikinScaleMetric (ξ : ℝ) : ℝ :=
  2 * (1 - (Real.tanh ξ) ^ 2)

/-- The Dikin ellipsoid of radius r centered at the equilibrium ξ = 0:
    ℰ(0, r) = { y ∈ ℝ | g(0) * y² ≤ r² }. -/
def dikinEquilibriumEllipsoid (r : ℝ) : Set ℝ :=
  { y : ℝ | dikinScaleMetric 0 * y ^ 2 ≤ r ^ 2 }

/-!
### 1. Dikin Barrier & Metric Properties
-/

/-- 🏆 THEOREM 1: The barrier potential Φ(ξ) reduces to 2 * ln(cosh(ξ)). -/
theorem dikin_barrier_eq_two_log_cosh (ξ : ℝ) :
    dikinScaleBarrier ξ = 2 * Real.log (Real.cosh ξ) := by
  unfold dikinScaleBarrier
  have h_cosh_pos : 0 < Real.cosh ξ := Real.cosh_pos ξ
  have h_id : 1 - (Real.tanh ξ) ^ 2 = 1 / (Real.cosh ξ) ^ 2 := by
    calc 1 - (Real.tanh ξ) ^ 2
      _ = 1 - (Real.sinh ξ / Real.cosh ξ) ^ 2 := by rw [Real.tanh_eq_sinh_div_cosh]
      _ = 1 - (Real.sinh ξ) ^ 2 / (Real.cosh ξ) ^ 2 := by rw [div_pow]
      _ = ((Real.cosh ξ) ^ 2 - (Real.sinh ξ) ^ 2) / (Real.cosh ξ) ^ 2 := by field_simp
      _ = 1 / (Real.cosh ξ) ^ 2 := by rw [Real.cosh_sq_sub_sinh_sq]
  rw [h_id, one_div, Real.log_inv, neg_neg, Real.log_pow, Nat.cast_ofNat]

/-- 🏆 THEOREM 2 (Strict Metric Positivity):
    The Dikin metric g(ξ) is strictly positive for all scale coordinates ξ ∈ ℝ. -/
theorem dikin_scale_metric_pos (ξ : ℝ) :
    0 < dikinScaleMetric ξ := by
  unfold dikinScaleMetric
  have h_tanh_sq := Real.tanh_sq_lt_one ξ
  have : 0 < 1 - (Real.tanh ξ) ^ 2 := by linarith
  linarith

/-- 🏆 THEOREM 3 (Equilibrium Metric Normalization):
    At the critical line equilibrium ξ = 0, the metric is normalized: g(0) = 2. -/
theorem dikin_scale_metric_at_zero :
    dikinScaleMetric 0 = 2 := by
  unfold dikinScaleMetric
  rw [Real.tanh_zero, sq, mul_zero, sub_zero, mul_one]

/-!
### 2. Dikin Confinement & Blahut-Arimoto Contraction
-/

/-- 🏆 THEOREM 4 (Equilibrium Ellipsoid Quadratic Bound):
    For any radius r > 0, the Dikin ellipsoid condition g(0) * y² ≤ r² is strictly 2 * y² ≤ r². -/
theorem dikin_equilibrium_ellipsoid_iff (r y : ℝ) :
    y ∈ dikinEquilibriumEllipsoid r ↔ 2 * y ^ 2 ≤ r ^ 2 := by
  unfold dikinEquilibriumEllipsoid
  rw [Set.mem_setOf_eq, dikin_scale_metric_at_zero]

/-- 🏆 THEOREM 5 (Blahut-Arimoto Geometric Contraction Step):
    If an operator 𝒯_BA contracts the scale coordinate by factor Kc ∈ [0, 1),
    |𝒯_BA(ξ)| ≤ Kc * |ξ|, then the contracted state maps strictly into a smaller Dikin ellipsoid:
    2 * (𝒯_BA(y))² ≤ Kc² * r² for all y in the r-ellipsoid. -/
theorem blahut_arimoto_dikin_shrinkage
    (Kc r y : ℝ) (hKc_nonneg : 0 ≤ Kc)
    (hy_in : y ∈ dikinEquilibriumEllipsoid r)
    (Ty : ℝ) (h_contraction : |Ty| ≤ Kc * |y|) :
    2 * Ty ^ 2 ≤ (Kc * r) ^ 2 := by
  have h_ellip := (dikin_equilibrium_ellipsoid_iff r y).mp hy_in
  have h_nonneg : 0 ≤ Kc * |y| := mul_nonneg hKc_nonneg (abs_nonneg y)
  have h_abs_sq : |Ty| ^ 2 ≤ (Kc * |y|) ^ 2 := by
    rw [sq, sq]
    exact mul_le_mul h_contraction h_contraction (abs_nonneg Ty) h_nonneg
  have h_sq : Ty ^ 2 ≤ (Kc * |y|) ^ 2 := by
    rw [← sq_abs Ty]
    exact h_abs_sq
  have h_kc_sq : (Kc * |y|) ^ 2 = Kc ^ 2 * y ^ 2 := by
    rw [mul_pow, sq_abs]
  rw [h_kc_sq] at h_sq
  have h_mult : 2 * Ty ^ 2 ≤ Kc ^ 2 * (2 * y ^ 2) := by
    calc 2 * Ty ^ 2
      _ ≤ 2 * (Kc ^ 2 * y ^ 2) := by linarith [h_sq]
      _ = Kc ^ 2 * (2 * y ^ 2) := by ring
  calc 2 * Ty ^ 2
    _ ≤ Kc ^ 2 * (2 * y ^ 2) := h_mult
    _ ≤ Kc ^ 2 * r ^ 2 := by
        have h_kc2_nonneg : 0 ≤ Kc ^ 2 := sq_nonneg Kc
        nlinarith
    _ = (Kc * r) ^ 2 := by ring

end

end InfoGeometry.Quantum.DikinApolloniusTrap
