import InfoGeometry.Canonical.SinkhornFoundation
import InfoGeometry.LLM.BogoliubovSinkhornRouting
import InfoGeometry.Inference.PoissonSinkhornPrimalDual
import InfoGeometry.Inference.PoissonSinkhornPotentials
import InfoGeometry.Probability.FiniteMarkovWeightedAdjoint
import InfoGeometry.Canonical.ThermodynamicChiralGraphCalculus
import InfoGeometry.Canonical.MaximumCaliberPath
import InfoGeometry.MassSpectrometry.DirectedOperatorDoubling
import InfoGeometry.MassSpectrometry.CausalCrossGramian
import InfoGeometry.MassSpectrometry.CausalTransferArchitecture
import InfoGeometry.Canonical.IBCanonical
import InfoGeometry.Canonical.IBTrajectory
import InfoGeometry.Canonical.IBFrozenModularBridge
import InfoGeometry.Canonical.RelationalInformationCore
import InfoGeometry.Canonical.ModularHessian
import InfoGeometry.InformationGeometry.BKMMetricModularBridge
import InfoGeometry.Canonical.BayesianThermoMetricHodgeBridge
import InfoGeometry.Dynamics.WassersteinProximalBridge
import InfoGeometry.Canonical.DikinFiniteOrbitColimit

noncomputable section

namespace InfoGeometry.LLM.McbalFullNativeCorridor

/-! ## Sinkhorn gauge fixing and Birkhoff geometry -/

/-- One Sinkhorn row/column step is exactly a two-sided diagonal Weyl gauge. -/
alias sinkhorn_two_step_is_weyl_gauge :=
  InfoGeometry.Canonical.MoE.sinkhornTwoStep_eq_weylGauge

/-- Every proof-carrying Sinkhorn-balanced switch has a convex permutation decomposition. -/
alias sinkhorn_balance_has_birkhoff_von_neumann_decomposition :=
  InfoGeometry.Canonical.MoE.exists_perm_decomposition_of_sinkhornBalanced

/-- A bistochastic balanced expert mixture is a convex mixture of permutation-routed outputs. -/
alias balanced_mixture_has_permutation_readback :=
  InfoGeometry.LLM.BogoliubovSinkhornRouting.sinkhornBalanced_permutation_decomposition

/-! ## Entropic primal/dual geometry -/

/-- A Poisson transport row is the unique positive entropy-regularized Gibbs minimizer. -/
alias poisson_row_assignment_is_unique_entropy_minimizer :=
  InfoGeometry.Inference.poissonTransportAssignment_unique_entropy_minimizer

/-- The finite Sinkhorn primal-minus-dual objective is exactly a Bregman gap. -/
alias poisson_sinkhorn_primal_dual_gap_is_bregman_gap :=
  InfoGeometry.Inference.poissonSinkhornPrimalDual_gap_eq_bregmanGap

/-- Consequently the finite Poisson-Sinkhorn primal/dual gap is nonnegative. -/
alias poisson_sinkhorn_primal_dual_gap_nonnegative :=
  InfoGeometry.Inference.poissonSinkhornPrimalDual_gap_nonneg

/-! ## Weighted adjoints, affinities, and Maximum Caliber -/

/-- Detailed balance is self-adjointness for the stationary weighted adjoint. -/
alias detailed_balance_iff_weighted_self_adjoint :=
  InfoGeometry.Probability.detailedBalance_iff_weightedAdjoint_eq

/-- Detailed balance is equivalently symmetry after stationary whitening. -/
alias detailed_balance_iff_whitened_symmetric :=
  InfoGeometry.Probability.detailedBalance_iff_whitened_symmetric

/-- Positive-rate path ratios are exponentials of the graph MaxCal constraint. -/
alias path_ratio_is_exponential_affinity_integral :=
  InfoGeometry.Canonical.MaximumCaliberPath.pathForwardBackwardRatio_eq_exp_maxCalConstraint

/-- Vanishing positive-cycle path entropy gives detailed balance on that cycle. -/
alias zero_cycle_affinity_implies_cycle_detailed_balance :=
  InfoGeometry.Canonical.MaximumCaliberPath.detailedBalanceOnCycle_of_pathEntropyProduction_eq_zero

/-! ## Directed and reciprocal Gramians in the mass-spectrometry lane -/

/-- Every directed operator is the sum of its reciprocal and oriented parts. -/
alias directed_operator_eq_symmetric_add_antisymmetric :=
  InfoGeometry.MassSpectrometry.symmetricPart_add_antisymmetricPart

/-- Transposition of a cross-Gramian exchanges its two feature slices. -/
alias cross_gramian_transpose_reverses_feature_slices :=
  InfoGeometry.MassSpectrometry.crossGramOperator_transpose

/-- The auto-Gramian slice has no oriented component. -/
alias auto_gramian_has_zero_antisymmetric_part :=
  InfoGeometry.MassSpectrometry.antisymmetricPart_crossGram_self_eq_zero

/-- A nonzero certified mass-spectrometry transfer strictly lowers physical mass. -/
alias nonzero_causal_transfer_strictly_lowers_mass :=
  InfoGeometry.MassSpectrometry.CausalTransferSystem.transfer_mass_decreases

/-! ## Frozen Information Bottleneck and modular KL potential -/

/-- The frozen BA modular potential is `beta * KL` plus the log-partition gauge. -/
alias frozen_ba_modular_potential_is_beta_kl_plus_partition_gauge :=
  InfoGeometry.Canonical.IB.ibBlahutArimotoStepFrozen_scalarModularPotential_eq_betaKL_add_logPartitionFrozen

/-- Removing the partition gauge leaves exactly the essential `beta * KL` generator. -/
alias frozen_ba_modular_potential_gauge_reduction :=
  InfoGeometry.Canonical.IB.ibBlahutArimotoStepFrozen_scalarModularPotential_sub_logPartitionFrozen_eq_betaKL

/-- The frozen BA step minimizes the supplied frozen variational functional. -/
alias frozen_ba_variational_descent :=
  InfoGeometry.Canonical.IB.frozenVariational_descent

/-- A subunit Lipschitz estimate yields convergence of the BA trajectory to a fixed point. -/
alias ib_trajectory_converges_under_subunit_lipschitz_bound :=
  InfoGeometry.Canonical.IB.tendsto_ibTrajectory_fixedPoint_of_lipschitz

/-! ## Operator information geometry and rotational/metric separation -/

/-- Comparison-state modular dynamics splits into gauge and source channels. -/
alias modular_dynamics_eq_gauge_add_source :=
  InfoGeometry.Canonical.RelationalInformationCore.comparisonInducedDynamics_eq_gauge_add_source

/-- The comparison phase form is the metric form twisted by the modular complex axis. -/
alias modular_phase_is_metric_twisted_by_complex_axis :=
  InfoGeometry.Canonical.RelationalInformationCore.comparisonPhaseReadout_eq_metric_comp_modularComplexI

/-- The BKM metric reduces to the classical Fisher metric on commuting diagonal observables. -/
alias bkm_reduces_to_classical_fisher_on_diagonal :=
  InfoGeometry.InformationGeometry.BKM.bkm_classical_fisher_reduction

/-! ## Bayesian Hodge decomposition -/

/-- A Bayesian posterior in the harmonic sector is orthogonal to exact and coexact errors. -/
alias harmonic_bayesian_posterior_is_locally_protected :=
  InfoGeometry.Canonical.BayesianThermoMetricHodgeBridge.posterior_harmonic_protected

/-- A calibrated coexact MaxCal current reads the logarithmic de Rham current. -/
alias coexact_maxcal_current_is_dlog_readout :=
  InfoGeometry.Canonical.BayesianThermoMetricHodgeBridge.coexact_current_eq_dlnQ

/-! ## Finite optimal-transport and interior-point envelopes -/

/-- Finite JKO-style proximal steps compose by addition of their time parameters. -/
alias jko_proximal_steps_form_additive_semigroup :=
  InfoGeometry.Dynamics.WassersteinProximalBridge.jkoEntropyStep_composition

/-- Contractive finite iterates remain in nested Dikin ellipsoids. -/
alias contractive_orbit_stays_in_nested_dikin_ellipsoids :=
  InfoGeometry.Canonical.DikinFiniteOrbitColimit.orbit_mem_dikin_ellipsoid

/-- The operator BKM-Dikin quadratic form is strictly positive off zero. -/
alias bkm_dikin_quadratic_is_positive_off_zero :=
  InfoGeometry.Canonical.DikinFiniteOrbitColimit.bkmDikinQuadratic_pos_of_ne_zero

end InfoGeometry.LLM.McbalFullNativeCorridor
