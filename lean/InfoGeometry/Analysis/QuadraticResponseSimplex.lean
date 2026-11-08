import InfoGeometry.Probability.SimplexQuadraticResponse
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Quadratic response in an internal coordinate

Exact scalar consequences of `C*X-B*X^2`. Positive rescaling of an internal
reference coordinate changes `C/B`, but preserves `B*X/C` and the response.
No measured distance, detector dimensions, or field-theoretic anomaly occurs
in these statements. CAS cross-check: `scripts/verify_simplex_response.py`.
-/

noncomputable section
namespace InfoGeometry.Analysis.QuadraticResponseSimplex

open InfoGeometry.Probability.SimplexQuadraticResponse

/-- Polynomial failure of homogeneity under a finite rescaling. -/
theorem response_dilation_defect (C B X a : ℝ) :
    response C B (a * X) - a * response C B X = -B * a * (a - 1) * X ^ 2 := by
  unfold response
  ring

/-- A reference-scale change is compensated by the fitted coefficients. -/
theorem response_coordinate_rescale (C B X a : ℝ) (ha : a ≠ 0) :
    response (C / a) (B / a ^ 2) (a * X) = response C B X := by
  unfold response
  field_simp

/-- Unlike the dimensional coordinate, the normalized coordinate is invariant. -/
theorem probability_coordinate_rescale (C B X a : ℝ) (ha : a ≠ 0) :
    (B / a ^ 2) * (a * X) / (C / a) = B * X / C := by
  by_cases hC : C = 0
  · simp [hC]
  · field_simp

/-- The extrapolated root rescales with the coordinate. -/
theorem root_coordinate_rescale (C B a : ℝ) (ha : a ≠ 0) :
    (C / a) / (B / a ^ 2) = a * (C / B) := by
  by_cases hB : B = 0
  · simp [hB]
  · field_simp

/-- Normalizing an observed-coordinate response gives the Bernoulli polynomial. -/
theorem normalized_response (C B X : ℝ) (hC : C ≠ 0) :
    B * response C B X / C ^ 2 = (B * X / C) * (1 - B * X / C) := by
  unfold response
  field_simp

/-- Equality at the maximum characterizes the unique turning coordinate. -/
theorem response_eq_maximum_iff (C B X : ℝ) (hB : 0 < B) :
    response C B X = C ^ 2 / (4 * B) ↔ X = C / (2 * B) := by
  have hgap := vertex_gap C B X hB.ne'
  constructor
  · intro h
    have hz : B * (X - C / (2 * B)) ^ 2 = 0 := by linarith
    have hs := (mul_eq_zero.mp hz).resolve_left hB.ne'
    nlinarith [sq_nonneg (X - C / (2 * B))]
  · rintro rfl
    simp only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at hgap
    linarith

/-- Response is nonnegative on its explicit simplex range. -/
theorem response_simplex_nonneg (C B p : ℝ) (hB : 0 < B)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ response C B (C / B * p) := by
  rw [probability_coordinate C B p hB.ne']
  exact mul_nonneg (div_nonneg (sq_nonneg C) hB.le)
    (mul_nonneg hp.1 (sub_nonneg.mpr hp.2))

/-- The relative response is the complementary normalized coordinate. -/
theorem response_survival (C B X : ℝ) (hC : C ≠ 0) (hX : X ≠ 0) :
    response C B X / (C * X) = 1 - B * X / C := by
  unfold response
  field_simp

theorem quadratic_le_rational_response (n τ : ℝ) (hn : 0 ≤ n) (hτ : 0 ≤ τ) :
    n - τ * n ^ 2 ≤ n / (1 + n * τ) := by
  have hd : 0 < 1 + n * τ := by positivity
  have hr := rational_residual n τ hd.ne'
  have hp : 0 ≤ τ ^ 2 * n ^ 3 / (1 + n * τ) := by positivity
  linarith

end InfoGeometry.Analysis.QuadraticResponseSimplex
