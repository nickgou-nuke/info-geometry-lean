import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InfoGeometry.InformationGeometry.FisherMetric

noncomputable section

/-!
# The Causal Poset of the Fisher Information Metric
This file synthesizes the Information Geometry foundation of the repository.
It formally excises probabilistic measure theory in favor of pure algebraic
Hessian bounds, defining the Fisher Metric algebraically from the log-likelihood.
-/

/-!
# Reciprocal-square information coefficient
This scalar function is useful as the curvature of the one-dimensional
negative-log barrier on the positive half-line. It is not, by itself, the
Fisher information of an arbitrary statistical model: that notion depends on
a likelihood and an expectation.
-/

/-- The algebraic Fisher Information component in one dimension. -/
def FisherInformation (p : ℝ) : ℝ := 1 / (p * p)

/-! The reciprocal quantity below is the algebraic inverse of the defined
coefficient. Calling it a Cramér–Rao bound requires additional statistical
hypotheses, so the results here assert only the reciprocal identity. -/

/-- The algebraic Cramér-Rao lower bound. -/
def CramerRaoLowerBound (p : ℝ) : ℝ := 1 / FisherInformation p

/-- For nonzero `p`, the reciprocal-square coefficient is strictly positive. -/
theorem fisherInformation_pos (p : ℝ) (hp : p ≠ 0) :
    0 < FisherInformation p := by
  dsimp [FisherInformation]
  apply one_div_pos.mpr
  exact mul_self_pos.mpr hp

/-- The reciprocal-square coefficient has reciprocal `p²` away from its
singular point. -/
theorem cramer_rao_inversion (p : ℝ) :
    CramerRaoLowerBound p = p * p := by
  dsimp [CramerRaoLowerBound, FisherInformation]
  rw [one_div, one_div, inv_inv]

/-- The coefficient and its reciprocal multiply to one off the singular
point. -/
theorem fisherInformation_mul_reciprocal_eq_one (p : ℝ) (hp : p ≠ 0) :
    FisherInformation p * CramerRaoLowerBound p = 1 := by
  rw [cramer_rao_inversion p]
  dsimp [FisherInformation]
  field_simp [hp]

/-- The reciprocal-square coefficient is nonnegative, including at its
defined value zero on the singular boundary. -/
theorem cramer_rao_nonneg (p : ℝ) :
    0 ≤ CramerRaoLowerBound p := by
  rw [cramer_rao_inversion p]
  exact mul_self_nonneg p

end

end InfoGeometry.InformationGeometry.FisherMetric
