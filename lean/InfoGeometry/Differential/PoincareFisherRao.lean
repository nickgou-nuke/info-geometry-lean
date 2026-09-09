/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace InfoGeometry.Differential.PoincareFisherRao

open Real Matrix

noncomputable section

/-!
# Fisher-Rao Information Metric on the Poincaré Upper Half-Plane

We formalize the Fisher-Rao information metric on the statistical manifold
of univariate Gaussian distributions $\mathcal{M} = \{(\mu, \sigma) \in \mathbb{R}^2 \mid \sigma > 0\}$,
which is isometrically identified with the Poincaré upper half-plane $\mathbb{H}^2$:
  ds² = (1 / y²) (dx² + dy²).

Formalized Core Properties:
1. Fisher metric tensor components: g₁₁ = 1/y², g₂₂ = 1/y², g₁₂ = g₂₁ = 0.
2. Metric positive-definiteness: vᵀ g v > 0 for all nonzero tangent vectors v.
3. Determinant and Log-Determinant potential: det(g) = 1/y⁴, Φ(y) = ln det(g) = -4 ln y.
4. Scale invariance under horizontal translations and hyperbolic dilations.
-/

/-- The Poincaré upper half-plane / Gaussian parameter domain ℍ² = {(x, y) ∈ ℝ² | y > 0}. -/
structure UpperHalfPlanePoint where
  x : ℝ
  y : ℝ
  y_pos : 0 < y

/-- The 2×2 Fisher-Rao metric matrix tensor at a point (x, y) ∈ ℍ²:
    g(x, y) = [[1/y², 0], [0, 1/y²]]. -/
def fisherMetricMatrix (p : UpperHalfPlanePoint) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![1 / p.y ^ 2, 0],
    ![0, 1 / p.y ^ 2]]

/-- Quadratic form: ds² = g(v, v) = (v_x² + v_y²) / y². -/
def fisherLineElement (p : UpperHalfPlanePoint) (vx vy : ℝ) : ℝ :=
  (vx ^ 2 + vy ^ 2) / p.y ^ 2

/-!
### 1. Matrix Representation and Strict Positive Definiteness
-/

/-- 🏆 THEOREM 1: The Fisher metric tensor evaluates to the diagonal components. -/
theorem fisher_metric_components (p : UpperHalfPlanePoint) :
    fisherMetricMatrix p 0 0 = 1 / p.y ^ 2 ∧
    fisherMetricMatrix p 1 1 = 1 / p.y ^ 2 ∧
    fisherMetricMatrix p 0 1 = 0 ∧
    fisherMetricMatrix p 1 0 = 0 := by
  unfold fisherMetricMatrix
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- 🏆 THEOREM 2: The quadratic form vᵀ · g · v equals the line element (vx² + vy²) / y². -/
theorem fisher_quadratic_form_eval (p : UpperHalfPlanePoint) (v : Fin 2 → ℝ) :
    dotProduct (mulVec (fisherMetricMatrix p) v) v = fisherLineElement p (v 0) (v 1) := by
  dsimp [dotProduct, mulVec, fisherMetricMatrix, fisherLineElement]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- 🏆 THEOREM 3: Strict positive-definiteness of the Fisher-Rao metric tensor for non-zero vectors. -/
theorem fisher_metric_pos_def (p : UpperHalfPlanePoint) (v : Fin 2 → ℝ) (hv : v ≠ 0) :
    0 < dotProduct (mulVec (fisherMetricMatrix p) v) v := by
  rw [fisher_quadratic_form_eval]
  unfold fisherLineElement
  have h_y_sq_pos : 0 < p.y ^ 2 := sq_pos_of_ne_zero (ne_of_gt p.y_pos)
  have h_vec_sq_pos : 0 < (v 0) ^ 2 + (v 1) ^ 2 := by
    have h_not_both_zero : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
      by_contra h_all_zero
      push_neg at h_all_zero
      apply hv
      ext i
      fin_cases i
      · exact h_all_zero.1
      · exact h_all_zero.2
    cases h_not_both_zero with
    | inl h0 =>
      have : 0 < (v 0) ^ 2 := sq_pos_of_ne_zero h0
      have : 0 ≤ (v 1) ^ 2 := sq_nonneg (v 1)
      linarith
    | inr h1 =>
      have : 0 ≤ (v 0) ^ 2 := sq_nonneg (v 0)
      have : 0 < (v 1) ^ 2 := sq_pos_of_ne_zero h1
      linarith
  exact div_pos h_vec_sq_pos h_y_sq_pos

/-!
### 2. Volume Form, Determinant, and Log-Determinant Potential
-/

/-- Determinant of the Fisher-Rao metric: det(g) = 1 / y⁴. -/
theorem fisher_metric_det (p : UpperHalfPlanePoint) :
    (fisherMetricMatrix p).det = 1 / p.y ^ 4 := by
  unfold fisherMetricMatrix
  rw [Matrix.det_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have : (p.y ^ 2) * (p.y ^ 2) = p.y ^ 4 := by ring
  rw [mul_zero, sub_zero, one_div_mul_one_div, this]

/-- Log-determinant metric potential: Φ(y) = ln det g(y) = -4 ln y. -/
theorem fisher_metric_log_det (p : UpperHalfPlanePoint) :
    Real.log (fisherMetricMatrix p).det = -4 * Real.log p.y := by
  rw [fisher_metric_det]
  have hp_pos : 0 < p.y := p.y_pos
  have hp4_pos : 0 < p.y ^ 4 := by positivity
  rw [one_div, Real.log_inv]
  have h_pow : Real.log (p.y ^ 4) = 4 * Real.log p.y := by
    rw [Real.log_pow p.y 4]
    push_cast
    ring
  rw [h_pow]
  ring

/-!
### 3. Hyperbolic Isometries: Horizontal Translation & Scaling
-/

/-- Horizontal translation isometry: (x, y) ↦ (x + c, y) leaves the metric invariant. -/
theorem fisher_metric_horizontal_translation_invariant
    (p : UpperHalfPlanePoint) (c : ℝ) :
    fisherMetricMatrix ⟨p.x + c, p.y, p.y_pos⟩ = fisherMetricMatrix p := by
  unfold fisherMetricMatrix
  rfl

/-- Hyperbolic scaling isometry: (x, y) ↦ (λ x, λ y) scales the line element by 1/λ². -/
theorem fisher_line_element_scaling
    (p : UpperHalfPlanePoint) (vx vy : ℝ) (lam_scale : ℝ) (h_lam : 0 < lam_scale) :
    fisherLineElement ⟨lam_scale * p.x, lam_scale * p.y, mul_pos h_lam p.y_pos⟩ (lam_scale * vx) (lam_scale * vy) =
    fisherLineElement p vx vy := by
  unfold fisherLineElement
  have h_num : (lam_scale * vx) ^ 2 + (lam_scale * vy) ^ 2 = lam_scale ^ 2 * (vx ^ 2 + vy ^ 2) := by ring
  have h_den : (lam_scale * p.y) ^ 2 = lam_scale ^ 2 * p.y ^ 2 := by ring
  rw [h_num, h_den]
  have h_scale_sq_pos : lam_scale ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_ne_zero (ne_of_gt h_lam))
  rw [mul_div_mul_left _ _ h_scale_sq_pos]

end

end InfoGeometry.Differential.PoincareFisherRao
