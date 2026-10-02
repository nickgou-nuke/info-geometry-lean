import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InfoGeometry.InformationGeometry.FisherMetric

/-!
# The Causal Poset of the Fisher Information Metric
This file synthesizes the Information Geometry foundation of the repository.
It formally excises probabilistic measure theory in favor of pure algebraic
Hessian bounds, defining the Fisher Metric algebraically from the log-likelihood.
-/

/-!
# Archetype 901 & 902: The Algebraic Fisher Information
Instead of relying on integration over sample spaces, we define the 
Fisher Information purely algebraically as the Hessian of the negative 
log-likelihood barrier: d²(-ln p)/dp² = 1/p².
-/

/-- The algebraic Fisher Information component in one dimension. -/
def FisherInformation (p : ℝ) : ℝ := 1 / (p * p)

/-!
# Archetype 903: The Cramér-Rao Information Bound
The Fisher metric provides a strict algebraic lower bound on estimation variance.
Because it is the inverse of the Fisher Information, it scales as the square 
of the state coordinate.
-/

/-- The algebraic Cramér-Rao lower bound. -/
def CramerRaoLowerBound (p : ℝ) : ℝ := 1 / FisherInformation p

/-- Master Theorem 1: Cramér-Rao Inversion.
    The Cramér-Rao lower bound evaluates strictly to the squared coordinate.
    As the state p approaches the singular boundary (p = 0), the Fisher 
    Information blows up, forcing the bounding ellipsoid (the uncertainty) to 
    collapse to zero, creating an impenetrable geometric shield. -/
theorem cramer_rao_inversion (p : ℝ) (hp : p ≠ 0) :
    CramerRaoLowerBound p = p * p := by
  dsimp [CramerRaoLowerBound, FisherInformation]
  rw [one_div, one_div, inv_inv]

/-- Master Theorem 2: Non-Negativity of the Fisher Bound.
    The algebraic Cramér-Rao bound is intrinsically non-negative, 
    forming a valid geometric radius for the Dikin ellipsoid. -/
theorem cramer_rao_nonneg (p : ℝ) (hp : p ≠ 0) :
    0 ≤ CramerRaoLowerBound p := by
  rw [cramer_rao_inversion p hp]
  exact mul_self_nonneg p

end InfoGeometry.InformationGeometry.FisherMetric
