import InfoGeometry.Detector.AmariHessianDuality
import InfoGeometry.Detector.AmariHessianDependency

open InfoGeometry.Canonical.AmariBinarySimplexBridge
open InfoGeometry.Detector.AmariLegendreCore
open InfoGeometry.Detector.AmariHessianDuality

example (coefficient efficiency : ℝ)
    (interior : coefficient * efficiency ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (deriv massieu) (naturalParameter coefficient efficiency) =
      coefficient * norm_single coefficient efficiency :=
  hessian_is_single_response coefficient efficiency interior

example : fisher_metric 2 (1 / 4) = 1 / 4 := by
  convert maximum_fisher_info_at_summit 2 (by norm_num) using 1
  norm_num

example : norm_single 2 (1 / 2) = 0 :=
  singles_at_boundary 2 (by norm_num)

example : 0 < fisher_metric 2 (1 / 2) :=
  fisher_metric_positive 2 (1 / 2)

example (probability : ℝ) (interior : probability ∈ Set.Ioo (0 : ℝ) 1) :
    IsGreatest (Set.range (fun parameter => parameter * probability - massieu parameter))
      (negativeEntropy probability) :=
  legendre_isGreatest interior

example (probability : ℝ) (interior : probability ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (deriv negativeEntropy) probability *
      deriv (deriv massieu) (logit probability) = 1 :=
  inverse_hessians interior

example :
    ¬ ProofDependency.Archetype.singlesMetricIdentity ≤ ProofDependency.Archetype.efficiencyPullback ∧
    ¬ ProofDependency.Archetype.efficiencyPullback ≤ ProofDependency.Archetype.singlesMetricIdentity := by
  decide

#print axioms hasDerivAt_massieu
#print axioms hasDerivAt_dual_gradient
#print axioms inverse_hessians
#print axioms massieu_strictConvex
#print axioms negativeEntropy_strictConvex
#print axioms log_logistic
#print axioms log_complement_logistic
#print axioms fenchel_gap_eq_binary_kl
#print axioms fenchel_gap_nonnegative
#print axioms legendre_isGreatest
#print axioms fisher_eq_expected_squared_score
#print axioms norm_single_eq
#print axioms partition_argument_simplification
#print axioms exp_naturalParameter
#print axioms massieu_naturalParameter
#print axioms expectation_eta_eq
#print axioms hessian_is_single_response
#print axioms fisher_metric_is_single_photopeak
#print axioms fisher_metric_positive
#print axioms fisher_metric_le_quarter
#print axioms fisher_metric_eq_quarter_iff
#print axioms maximum_fisher_info_at_summit
#print axioms hasDerivAt_naturalParameter
#print axioms fisher_efficiency_pullback
#print axioms singles_at_boundary
#print axioms no_finite_natural_parameter_at_boundary
#print axioms ProofDependency.hessian_branch
#print axioms ProofDependency.legendre_branch
#print axioms ProofDependency.coordinate_readouts_incomparable
#print axioms ProofDependency.no_cycle
