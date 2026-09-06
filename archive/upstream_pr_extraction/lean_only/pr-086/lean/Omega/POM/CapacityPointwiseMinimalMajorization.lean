import Mathlib.Tactic
import Omega.Conclusion.CapacityMajorizationSchurHardness

namespace Omega.POM

/-- Paper label: `cor:pom-capacity-pointwise-minimal-majorization`. -/
theorem paper_pom_capacity_pointwise_minimal_majorization
    (extremizer competitor : List ℝ) :
    (∀ u : ℝ, Omega.Conclusion.capacityCurve extremizer u ≤
      Omega.Conclusion.capacityCurve competitor u) ↔
      Omega.Conclusion.majorizes extremizer competitor := by
  simpa using
    (Omega.Conclusion.paper_conclusion_capacity_majorization_schur_hardness extremizer
      competitor).symm

end Omega.POM
