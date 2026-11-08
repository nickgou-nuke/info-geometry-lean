import Mathlib.Tactic
import Omega.Discussion.HypercubePotentialCurvatureControlledStrictification
import Omega.Discussion.SquierCurvatureHolonomyStokes

namespace Omega.Discussion

/-- Paper-facing zero-curvature strictification criterion: vanishing Squier curvature is
equivalent to admitting a potential, and a potential yields the strictification torsor. -/
theorem paper_discussion_squier_zero_curvature_strictification
    (zeroCurvature hasPotential strictificationTorsor : Prop)
    (vanishingClassCriterion : zeroCurvature ↔ hasPotential)
    (exactnessToStrictification : hasPotential → strictificationTorsor) :
    (zeroCurvature ↔ hasPotential) ∧
      (hasPotential → strictificationTorsor) := by
  exact ⟨vanishingClassCriterion, exactnessToStrictification⟩

end Omega.Discussion
