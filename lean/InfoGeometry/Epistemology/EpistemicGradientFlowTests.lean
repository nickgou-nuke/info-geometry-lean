import InfoGeometry.Epistemology.EpistemicGradientFlowDependency

open InfoGeometry.Canonical.AmariBinarySimplexBridge
open InfoGeometry.Geometry.BinaryLegendreEntropyFlow
open InfoGeometry.Epistemology.EpistemicGradientFlow
open InfoGeometry.Epistemology.DiracRelativeEntropyBoundary
open Filter
open scoped Topology ENNReal

example (initial time : ℝ) :
    0 ≤ relativeEntropy initial time ∧
      relativeEntropy initial time ≤ initial ^ 2 / 4 * Real.exp (-2 * time) :=
  relativeEntropy_exponential_bound initial time

example (initial time : ℝ) :
    deriv (relativeEntropy initial) time =
      -fisherMix (entropyRelaxation initial time) * (deriv (entropyRelaxation initial) time) ^ 2 :=
  relativeEntropy_dissipation initial time

example (initial : ℝ) : Tendsto (relativeEntropy initial) atTop (𝓝 0) :=
  relativeEntropy_tendsto_zero initial

example (initial : ℝ) : Tendsto (entropyRelaxation initial) atTop (𝓝 (1 / 2 : ℝ)) :=
  relaxation_tendsto_midpoint initial

example : InfoGeometry.KL.kl_div
    (MeasureTheory.Measure.dirac (0 : ℝ)) (MeasureTheory.Measure.dirac 1) = ∞ :=
  dirac_to_distinct_dirac 0 1 (by norm_num)

#print axioms logistic_quarter_lipschitz
#print axioms midpoint_entropy_quadratic_bound
#print axioms relativeEntropy_eq_binary_kl
#print axioms hasDerivAt_relativeEntropy
#print axioms relativeEntropy_dissipation
#print axioms relativeEntropy_antitone
#print axioms relativeEntropy_exponential_bound
#print axioms relaxation_tendsto_midpoint
#print axioms relativeEntropy_tendsto_zero
#print axioms kl_to_dirac_eq_top_of_mass_outside
#print axioms dirac_to_distinct_dirac
#print axioms ProofDependency.analytic_branches
#print axioms ProofDependency.dissipation_and_rate_incomparable
#print axioms ProofDependency.dirac_obstruction_is_separate
#print axioms ProofDependency.no_cycle
