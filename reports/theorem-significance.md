# Theorem Significance Report

**Theorems scored:** 5055  
**With violations:** 2467 (1526 error, 941 warning-only)  
**Clean:** 2588  

## Tag Distribution

| Tag | Count |
|-----|-------|
| `dead-candidate` | 3148 |
| `proof-infrastructure` | 1797 |
| `auto-generated` | 1321 |
| `wrapper-candidate` | 1262 |
| `rfl-like` | 166 |
| `statement-bearing` | 110 |
| `role-exempt` | 32 |
| `high-fan-in` | 22 |
| `attr:infrastructure` | 16 |
| `attr:expository` | 15 |
| `capstone-candidate` | 4 |
| `attr:terminal` | 1 |

## Violation Distribution

| Violation | Count |
|-----------|-------|
| `V2/dead-public-theorem` | 1874 |
| `V1/public-wrapper-inflation` | 1229 |
| `V4/bridge-infrastructure-promoted` | 296 |
| `V0/syntactic-vacuity` | 64 |

## Errors (require action)

### `lean/InfoGeometry/Canonical/AQFTOperatorEndpoints.lean`

- **`InfoGeometry.Canonical.AQFTOperatorInterface.grandCanonicalEulerStep_eq_of_vacuumSplit`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.RicciMongeAmpere.VacuumEinsteinOnTransportedSplit`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.AQFTOperatorInterface.ibWeightedKMSClosure_of_jointKernel_commutator`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.KMSSinkhornBridge.CommutatorOrthogonalOnOmega`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/AQFTReadiness.lean`

- **`InfoGeometry.Canonical.AQFTOperatorInterface.AQFTReadinessPackage.isCStarReadyF`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AQFTOperatorInterface.AQFTReadinessPackage.isCompleteCStarReadyE`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AQFTOperatorInterface.AQFTReadinessPackage.projectorSuperPair`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ActionDuality.lean`

- **`InfoGeometry.Canonical.ActionDuality.einsteinHilbertAction_and_zeroGap_of_compatible`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ActionDuality.einsteinHilbertAction_eq_neg_six_dual_pairing_sub_dual_of_compatible`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/AnalyticalIndexCapstone.lean`

- **`InfoGeometry.Canonical.AnalyticalIndex.FullThermoGeoIndexCapstone.geometricAlgebraicState`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.FullThermoGeoIndexCapstone.thermodynamicKMSState`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.SinkhornKMSCapstone.kmsState`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.fullThermoGeoIndexCapstone_of_states`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.sinkhornIterate_sinkhornKMSCapstone_of_closure`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean`

- **`InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex_eq_of_chiralParts_eq`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.AnalyticalIndex.chiralKernelSliceMinus`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.chiralNoZeroCrossingAlong_of_gap`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.AnalyticalIndex.chiralKernelSliceMinus`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.chiralPartMinus_eq_projectorPlus_comp_of_anticommute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.chiralPartPlus_eq_projectorMinus_comp_of_anticommute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.chiralProjectorMinus_comp_self_of_square_eq_id`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.chiralProjectorPlus_comp_self_of_square_eq_id`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.chiralSliceIsoAlong_of_modularCliffordTransport`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.AnalyticalIndex.chiralSliceIsoAlong_of_modularCliffordUnitTransport`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.chiralSliceIsoAlong_of_noZeroCrossing`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.AnalyticalIndex.chiralSliceIsoAlong_of_const_finrank`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.chiralSliceIsoAlong_of_noZeroEigenCrossing_path`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.BottDirac.Endomorphism`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.cl11_bottDirac_sq_eq_zero_of_laplacian_zero`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.BottDirac.cl11BottLaplacian`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.dirac_eq_of_chiralParts_eq`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.AnalyticalIndex.chiralPartPlus`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.indexInvariantAlong_of_modularCliffordTransport_components`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.AnalyticalIndex.chiralKernelSliceMinus`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.indexInvariantAlong_of_noZeroEigenCrossing_path`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.BottDirac.Endomorphism`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/AnalyticalIndexCoupled.lean`

- **`InfoGeometry.Canonical.AnalyticalIndex.sinkhornRicciIndexInvariant_of_conjugacy_state_hypotheses`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.sinkhornRicciIndexInvariant_of_modularCliffordTransport_components_state_hypotheses`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.sinkhornRicciIndexInvariant_of_modularCliffordTransport_state_hypotheses`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/AnomalyGauge.lean`

- **`InfoGeometry.Canonical.AnomalyGauge.anomaly_generates_isometry`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AnomalyGauge.skew_adjoint_is_krein_skew_adjoint`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Singular.Architecture.IsKreinSkewAdjointH`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/AnomalyInflow.lean`

- **`InfoGeometry.Canonical.AnomalyInflow.anomalyInflowClosure`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AnomalyInflow.boundaryAnomaly_eq_zero`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.TopologicalInvariants.BayesianLoop`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean`

- **`InfoGeometry.Canonical.MoE.arnoldNetworkOutput_eq_of_experts_fix`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.MoE.normalizedWeights_sum_one`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.arnoldNetwork_preserves_base`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.arnoldNetwork_preserves_transportWeylMinus`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ArnoldMajoranaCarrier`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.arnoldNetwork_preserves_transportWeylMinus_and_ker_of_linearExperts_commuting`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.arnoldNetwork_preserves_transportWeylMinus_nonzero_ker_of_experts_fix`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ArnoldMajoranaCarrier`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.arnoldNetwork_preserves_transportWeylMinus_of_linearExperts_commute_transportJ`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ArnoldMajoranaCarrier`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.arnoldNetwork_preserves_transportWeylPlus`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ArnoldMajoranaCarrier`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.arnoldNetwork_preserves_transportWeylPlus_and_ker_of_linearExperts_commuting`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.arnoldNetwork_preserves_transportWeylPlus_nonzero_ker_of_experts_fix`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ArnoldMajoranaCarrier`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.arnoldNetwork_preserves_transportWeylPlus_of_linearExperts_commute_transportJ`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ArnoldMajoranaCarrier`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.exists_network_fixed_transportWeylMinus_nonzero_ker_of_experts_fix_of_simplifiedBoundaryModel_under_bogoliubov`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.exists_network_fixed_transportWeylMinus_nonzero_ker_of_experts_fix_of_weylZeroModePair`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.RealMajorana.RealBogoliubovTransform.B`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.exists_network_fixed_transportWeylPlus_nonzero_ker_of_experts_fix_of_simplifiedBoundaryModel_under_bogoliubov`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.exists_network_fixed_transportWeylPlus_nonzero_ker_of_experts_fix_of_weylZeroModePair`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.RealMajorana.RealBogoliubovTransform.B`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.expert_apply_mem_transportWeylMinus_of_clm_commutes_transportJ`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.ArnoldMajoranaCarrier`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.expert_apply_mem_transportWeylPlus_of_clm_commutes_transportJ`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.ArnoldMajoranaCarrier`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/Attention.lean`

- **`InfoGeometry.Canonical.Attention.attentionWeights_sum_one`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.Attention.ContextWindow`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/AttentionEuclidean.lean`

- **`InfoGeometry.Canonical.Attention.euclideanAttentionWeights_sum_one`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.Attention.ContextWindow`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/AttentionPolarizedGibbsBridge.lean`

- **`InfoGeometry.Canonical.Attention.partition_polarizedPlusParams_eq_logitSum`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Attention.polarizedPlusAttentionHead_eq_gibbsExpectation`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.Attention.ContextWindow`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.Attention.polarizedPlusAttentionWeights_eq_euclideanGibbsWeights_of_constantKeyNorm`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.Attention.polarizedPlusAttentionWeights_eq_euclideanAttentionWeights_of_constantKeyNorm`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.Attention.polarizedPlusParams_energy`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Attention.polarizedPlusParams_energy_eq_neg_dot_plus_half_norms`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.Attention.ContextWindow`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/AttentionPolarizedSinkhornBridge.lean`

- **`InfoGeometry.Canonical.Attention.exists_perm_decomposition_of_bistochastic_polarizedPlusAttention`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.Attention.ContextWindow`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.Attention.polarizedPlusAttentionMatrix_mem_rowStochastic`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/AttentionPolarizedSplit.lean`

- **`InfoGeometry.Canonical.Attention.polarizedPlusAttentionHead_eq_euclideanAttentionHead_of_constantKeyNorm`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.Attention.polarizedPlusAttentionWeights_eq_euclideanAttentionWeights_of_constantKeyNorm`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.Attention.polarizedPlusAttentionWeights_sum_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/AttentionSplit.lean`

- **`InfoGeometry.Canonical.Attention.lorentzianAttentionWeights_sum_one`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.Attention.ContextWindow`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/BekensteinBound.lean`

- **`InfoGeometry.Canonical.BekensteinBound.cocycleIncrement_abs_le_trajectoryRNBarrier_of_connesCocycle_generatorLift`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BekensteinBound.relEnt_drop_nonneg_of_casiniIncrementBridge`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Volume.ConnesCocycle.AlgebraEnd`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BekensteinBound.topologicalBekensteinBound_of_connesCocycle`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.BekensteinBound.CocycleEntropyPotential`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BekensteinBound.topologicalBekensteinBound_of_connesCocycle_natMatch`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BekensteinBound.topologicalBekensteinBound_of_sinkhornTrajectory`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.BekensteinBound.trajectoryRNBarrier_nonneg`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BekensteinBound.topologicalBekensteinBound_of_tomitaConnesCocycle_casiniIncrement`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.BekensteinBound.topologicalBekensteinBound_of_connesCocycle_casiniIncrement`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BekensteinBound.topologicalBekensteinBound_of_tomitaConnesCocycle_generatorLift`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.BekensteinBound.TomitaCocycleEntropyPotential`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/BeliefAlgebra.lean`

- **`InfoGeometry.Canonical.BeliefAlgebra.BeliefSystem.non_commutative_updates`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.InformationTorsion.TwistedInference.has_torsion`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/BerryPhase.lean`

- **`InfoGeometry.Canonical.BerryPhase.berryPhase_ne_zero_of_anomaly_flux_ne_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.berry_phase_vanishes_for_normal`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.informationBerryPhase_eq_loopLength_mul_chiralAnomalyIndex`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.informationBerryPhase_eq_loopLength_mul_epsilon_mul_rank`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.informationBerryPhase_ne_zero_of_loopLength_ne_zero_of_chiralAnomalyIndex_ne_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/BogoliubovClosedForms.lean`

- **`InfoGeometry.Canonical.BogoliubovClosedForms.JBoost_apply`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovClosedForms.JBoost_eq_cosh_add_sinh_J`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.BogoliubovClosedForms.exp_eq_cosh_add_sinh_of_sq_eq_one`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovClosedForms.KRotation_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovClosedForms.KRotation_eq_cos_add_sin_K`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.BogoliubovClosedForms.exp_eq_cos_add_sin_of_sq_eq_neg_one`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovClosedForms.epsilonBoost_apply`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovClosedForms.epsilonBoost_eq_cosh_add_sinh_eps`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.BogoliubovClosedForms.exp_eq_cosh_add_sinh_of_sq_eq_one`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovClosedForms.epsilon_comp_JBoost`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovClosedForms.epsilon_comp_KRotation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovClosedForms.epsilon_comp_epsilonBoost`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovClosedForms.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/BogoliubovFockSuper.lean`

- **`InfoGeometry.Canonical.BogoliubovFockSuper.HyperbolicMixingParams.normalization`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.anticommutator_ofAngle_projector_model`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.anticommutator_symm`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.bogoliubovAnnihilation_kills_vacuumVector`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.BogoliubovFockSuper.HyperbolicMixingParams`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.bogoliubovCreation_kills_vacuumVector`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.BogoliubovFockSuper.HyperbolicMixingParams`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.car_realization_of_clifford`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.cliffordConcreteAnnihilation_apply_to_doubled`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.RealMajoranaCategory.cl11DoubledCore`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.cliffordConcreteCreation_apply_to_doubled`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.RealMajoranaCategory.cl11DoubledCore`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.cliffordConcreteIsCARPair`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.commutator_annihilation_self`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.BogoliubovFockSuper.SuperParity.even`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.commutator_creation_self`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.BogoliubovFockSuper.SuperParity.even`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.commutator_swap`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.BogoliubovFockSuper.SuperParity.even`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.einsteinFockDeformation_eq_zero_of_vacuumTransported`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.RicciMongeAmpere.VacuumEinsteinOnTransportedSplit`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.fockAnticommutator_symm`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.BogoliubovFockSuper.anticommutator_symm`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.fockCommutator_swap`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.BogoliubovFockSuper.commutator_swap`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.grandCanonicalFockGenerator_eq_hamiltonian_of_vacuumTransported`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.RicciMongeAmpere.VacuumEinsteinOnTransportedSplit`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.grandCanonicalGenerator_eq_hamiltonian_of_vacuumTransported`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.BogoliubovFockSuper.HyperbolicMixingParams`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.inducedChemicalPotential_eq_zero_of_vacuumTransported`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.isCARPair_of_linear_CARWitness`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Quantum.RealMajoranaCategory.cl11DoubledCore`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.not_isCARPair_base`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.projectorSuperPair_of_chiralityPolarization`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/BogoliubovPolarizationBridge.lean`

- **`InfoGeometry.Canonical.BogoliubovPolarizationBridge.bogoliubovPolarizationBridge_of_strictSymmetry`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovPolarizationBridge.car_realization_of_strictSymmetryBogoliubov`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.RealMajorana.PolarizedMajorana`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovPolarizationBridge.projectorSuperPair_of_targetPolarization`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Quantum.RealMajorana.PolarizedMajorana`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovPolarizationBridge.transportK_sq_of_strictSymmetryBogoliubov`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Quantum.RealMajorana.PolarizedMajorana`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovPolarizationBridge.transportP_eq_targetPolarization_of_strictSymmetry`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Quantum.RealMajorana.PolarizedMajorana`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/BogoliubovProjectorFlux.lean`

- **`InfoGeometry.Canonical.BogoliubovProjectorFlux.minusProjectorFlux_JBoost`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorFlux.minusProjectorFlux_KRotation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorFlux.plusProjectorFlux_JBoost`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorFlux.plusProjectorFlux_KRotation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorFlux.transportedMinusProjector_JBoost`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.BogoliubovProjectorTransport.spectralMinusProj_comp_JBoost`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorFlux.transportedMinusProjector_KRotation`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorFlux.transportedMinusProjector_epsilonBoost`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorFlux.transportedPlusProjector_JBoost`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorFlux.transportedPlusProjector_KRotation`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorFlux.transportedPlusProjector_epsilonBoost`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/BogoliubovProjectorTransport.lean`

- **`InfoGeometry.Canonical.BogoliubovProjectorTransport.epsilonBoost_preserves_minusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorTransport.epsilonBoost_preserves_plusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorTransport.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorTransport.modularComplexI_maps_minusSheet_to_plusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorTransport.modularComplexI_maps_plusSheet_to_minusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorTransport.modularConjugationJ_maps_minusSheet_to_plusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorTransport.modularConjugationJ_maps_plusSheet_to_minusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorTransport.modularTransportFlow_deriv`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.BogoliubovProjectorTransport.instNormedRingContinuousLinearMapRealIdDoubledSpace`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorTransport.spectralMinusProj_comp_J`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.BogoliubovProjectorTransport.instNormedRingContinuousLinearMapRealIdDoubledSpace`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorTransport.spectralPlusProj_commutes_modularTransportFlow`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorTransport.spectralPlusProj_comp_J`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.BogoliubovProjectorTransport.instNormedRingContinuousLinearMapRealIdDoubledSpace`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorTransport.spectralPlusProj_comp_modularTransportFlow`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/BogoliubovTransport.lean`

- **`InfoGeometry.Canonical.BogoliubovTransport.JBoost_add`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.JBoost_zero`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.KRotation_add`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.KRotation_zero`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.epsilonBoost_add`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.epsilonBoost_zero`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.heisenbergKreinTransport_split_generator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.kreinExpectation_add`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instKreinSpaceProdL2`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.kreinExpectation_neg`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instKreinSpaceProdL2`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.kreinExpectation_one`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.KreinSpace.kreinInner`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.kreinExpectation_smul`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instKreinSpaceProdL2`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.modularTransportFlow_add`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.modularTransportFlow_zero`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.modularVariance_of_normalized`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.neg_phaseAxis_comp_phaseConjugate`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.neg_phaseConjugate_comp_phaseAxis`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.phaseAxisForce_add`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.phaseAxisForce_smul`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.phaseAxisTransport_eq_from_phaseAntilinearPart`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.phaseAxisTransport_eq_zero_of_IsPhaseLinear`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.transportCommutator_split_generator`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.BogoliubovTransport.phaseLinearPart_add_phaseAntilinearPart`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/BottDirac.lean`

- **`InfoGeometry.Canonical.BottDirac.bottDirac_apply_tmul`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BottDirac.bottDirac_sq_eq_sum_laplacians`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.BottDirac.bottDirac_sq_eq_sum_laplacians_tmul`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BottDirac.cl11DiracSeed_involutive`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BottDirac.cl11_bottDirac_sq_eq_cl11BottLaplacian`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.BottDirac.cl11BottLaplacian`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BottDirac.cl22_bottDirac_sq_eq_cl22BottLaplacian`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BottDirac.cl22_bottDirac_sq_eq_two_tensor_id`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BottDirac.spectralDiracLinear_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/BottPeriodicity.lean`

- **`InfoGeometry.Canonical.BottPeriodicity.bottGeneratorInjection_zero_left`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.CliffordTower.splitSpaceModule`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BottPeriodicity.bottGeneratorInjection_zero_right`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.CliffordTower.splitSpaceModule`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BottPeriodicity.bottStepEquiv_symm_left_generator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BottPeriodicity.bottStepEquiv_symm_right_generator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BottPeriodicity.firstBottStep_consumes_doubledSpaceCl11Action_J`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BottPeriodicity.firstBottStep_consumes_doubledSpaceCl11Action_K`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BottPeriodicity.gradedProdInjection_matches_pattern_unit`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.CliffordTower.splitSpaceModule`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.BottPeriodicity.gradedProdInjection_on_generator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BottPeriodicity.tensorModularJ_comp_tmul`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BottPeriodicity.tensorModularJ_tmul`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BottPeriodicity.tensorSpectralEpsilon_comp_tmul`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BottPeriodicity.tensorSpectralEpsilon_tmul`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/CalabiYauMetricRicci.lean`

- **`InfoGeometry.Canonical.CalabiYauBridge.MetricDerivedRNRicciBridge.metricLogDetTwiceDifferentiable`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CalabiYauBridge.MetricDerivedRNRicciBridge.ofUnitRelativeVolume_fderiv`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry.H`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.CalabiYauBridge.isRicciFlat_of_unitRelativeVolume`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry.H`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.CalabiYauBridge.vacuumEinsteinEquation_of_unitRelativeVolume`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry.H`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.CalabiYauBridge.vacuumEinsteinEquation_of_unitRelativeVolume_metricDerived`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry.H`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/CalabiYauRNMongeAmpere.lean`

- **`InfoGeometry.Canonical.CalabiYauBridge.log_mongeAmpereDensity_eq_neg_kahlerPotentialRN_of_rnEntropySource`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry.H`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.CalabiYauBridge.rnEntropySourcesMongeAmperePotential`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry.H`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.CalabiYauBridge.rnEntropySourcesMongeAmperePotential_of_logF_eq_neg_kahlerPotentialRN`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry.H`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/CalabiYauSingularBridge.lean`

- **`InfoGeometry.Canonical.CalabiYauSingularTransportBridge.isRicciFlat_and_logDivergence_eq_projective_nilpotent_graded_of_unitRelativeVolume_metricDerived_of_boundaryScale_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CalabiYauSingularTransportBridge.isRicciFlat_and_logDivergence_eq_singularComplement_of_unitRelativeVolume_metricDerived`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CalabiYauSingularTransportBridge.vacuumEinsteinEquation_and_logDivergence_eq_projective_nilpotent_graded_of_unitRelativeVolume_metricDerived_of_boundaryScale_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CalabiYauSingularTransportBridge.vacuumEinsteinEquation_and_logDivergence_eq_singularComplement_of_unitRelativeVolume_metricDerived`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/CartanBerezinianCore.lean`

- **`InfoGeometry.Canonical.CartanBerezinianCore.generalizedBerezinianScale_eq_restrictedVolumeScale`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.RestrictedVolumeCharacter.RestrictedSheetEquiv.restrictedVolumeCharacter`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.CartanBerezinianCore.generalizedBerezinian_diagonal_reduction`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CartanBerezinianCore.schur_eq_plusBlock_of_offDiagonal_vanish`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.MongeAmpereDualSheetBridge.minusToPlusBlockMap`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/CartanDecomposition.lean`

- **`InfoGeometry.Canonical.CartanDecomposition.InformationCartanTriple.grading_commutator_anomaly`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CartanDecomposition.InformationCartanTriple.spectral_proj_is_compact_of_normal`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/CayleyBregmanBridge.lean`

- **`InfoGeometry.Canonical.Cayley.Bridge.left_inv`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Cayley.Bridge.right_inv`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Cayley.cayleyNegationPythagoreanInvariance`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.Cayley.cayley_pythagorean_invariance`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.Cayley.cayleyPythagoreanInvariance`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.Cayley.Transport`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.Cayley.grad_transport_back`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.Cayley.Bridge.equiv`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.Cayley.quadraticDualFlat_divergence`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Geometry.DualFlat.divergence`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.Cayley.quadraticDualFlat_nabla`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ChiralAnomaly.lean`

- **`InfoGeometry.Canonical.ChiralAnomaly.exists_routingEpsilon_of_mem_doublyStochastic`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.MoE.PermMode`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ChiralAnomaly.normal_inverse_anomaly_vanishes`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ChiralAnomaly.routingEpsilon_eq_semantic_gap_abs`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.MoE.cliffordSemanticState`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ChiralAnomaly.sinkhornIterate_generator_step_control`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.MoE.trajectoryRNBarrierNext`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ChiralAnomaly.sinkhornIterate_step_control`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.MoE.trajectoryLyapunov`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ChiralAnomaly.sinkhornPermutationWeights_decomposition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ChiralEinsteinBridge.lean`

- **`InfoGeometry.Canonical.ChiralEinsteinBridge.anomalyDrivenScalarRicci_fixedpoint_tracks_source`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ChiralEinsteinBridge.SatisfiesAnomalyDrivenScalarRicciFlow`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ChiralEinsteinBridge.anomalyDriven_fixedpoint_eq_inverseEpsilon`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.RicciMongeAmpere.ScalarRicciFlow`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ChiralEinsteinBridge.anomalyDriven_zeroSource_iff_normalized`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ChiralEinsteinBridge.anomalyStressEnergyAt_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ChiralEinsteinBridge.anomalyStressEnergyAt_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ChiralEinsteinBridge.einsteinEquation_of_anomaly_source`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.ChiralEinsteinBridge.anomalyStressEnergyAt`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ChiralEinsteinBridge.exists_einsteinEquation_of_bistochastic_routingAnomaly`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ChiralGravity.lean`

- **`InfoGeometry.Canonical.ChiralGravity.anomalyEinsteinResidualAt_def`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ChiralGravity.anomaly_nonzero_excludes_vacuum`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ChiralEinsteinBridge.anomalyStressEnergyAt`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ChiralGravity.routingAnomaly_nonzero_forces_curved_plus_component`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ChiralEinsteinBridge.anomalyStressEnergyModelAt`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/ChiralRGFlow.lean`

- **`InfoGeometry.Canonical.ChiralRGFlow.ChiralAsymptoticModel.beta_eq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ChiralRGFlow.ChiralAsymptoticModel.gamma_pos`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ChiralRGFlow.asymptotic_freedom_of_negative_beta`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ChiralRGFlow.ChiralAsymptoticModel.asymptotic`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/ChiralTorsionGeneralizedKL.lean`

- **`InfoGeometry.Canonical.ChiralTorsionBridge.gibbsSmoothingOnGeneralizedKL_nonneg`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ChiralTorsionBridge.gibbsSmoothingOnGeneralizedKL_pos`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/ChiralTorsionState.lean`

- **`InfoGeometry.Canonical.ChiralTorsionBridge.chentsov_and_gibbs_of_state`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ChiralTorsionBridge.torsion_nonzero_of_state_and_chiral`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ConformalUnification.ConformalInference`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ChiralTorsionBridge.twistedInference_torsion_nonzero`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.InformationTorsion.TwistedInference.has_torsion`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/CliffordBridge.lean`

- **`InfoGeometry.Canonical.CliffordBridge.q_agrees_with_Gauge_quad`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.Gauge.quad`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.CliffordBridge.splitBilinear_eq_gaugeBilinear`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.CliffordBridge.B_agrees_with_Gauge_bilinear`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.CliffordBridge.splitQuadratic_eq_gaugeQuadratic`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.CliffordBridge.q_agrees_with_Gauge_quad`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/CoarseGraining.lean`

- **`InfoGeometry.Canonical.FiniteCoarseGraining.fiberWeight_singleton_eq_totalWeight`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.FiniteCoarseGraining.totalWeight_eq_sum_fiberWeight`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.encoderMarginal_apply`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.encoderMarginal`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/ConformalAlgebra.lean`

- **`InfoGeometry.Canonical.ConformalAlgebra.ConformalBeliefAlgebra.D_eq_CI_D`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ConformalAlgebra.ConformalBeliefAlgebra.D_def`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ConformalAlgebra.ConformalBeliefAlgebra.cartanInvolution_eq_neg_self_iff_weylDilation_of_gradingInvolutive`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalAlgebra.ConformalBeliefAlgebra.cartanInvolution_eq_self_iff_volumePreserving_of_gradingInvolutive`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalAlgebra.ConformalBeliefAlgebra.cartanInvolution_involutive_of_gradingInvolutive`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalAlgebra.ConformalBeliefAlgebra.cartan_generator_split`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalAlgebra.ConformalBeliefAlgebra.commutator_volumePreserving_volumePreserving`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalAlgebra.ConformalBeliefAlgebra.commutator_volumePreserving_weylDilation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalAlgebra.ConformalBeliefAlgebra.commutator_weylDilation_weylDilation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalAlgebra.ConformalBeliefAlgebra.generatorCartanDecomposition_iff`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalAlgebra.ConformalBeliefAlgebra.generatorCartanDecomposition_of_parts`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalAlgebra.ConformalBeliefAlgebra.scale_anomaly_breaks_weight_closure`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.ConformalAlgebra.ConformalBeliefAlgebra.scale_anomaly_emergence`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ConformalAlgebra.ConformalBeliefAlgebra.scale_anomaly_emergence`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.ConformalAlgebra.ConformalBeliefAlgebra.CI`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ConformalAlgebra.ConformalBeliefAlgebra.scale_anomaly_obstructs_weyl_flatness`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ConformalAlgebra.ConformalBeliefAlgebra.scale_anomaly_breaks_weight_closure`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/ConformalAnomalySource.lean`

- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.anomalyDrivenScalarRicciFlow_of_kahlerLogDet_normalized`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.ConformalUnification.ConformalInference`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.chiralAnomalyOperator_eq_zero_of_unitRelativeVolume`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.chiralAnomaly_eq_zero_of_kahlerLogDet_normalized_fixedpoint`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.chiralScale_eq_projectorObstruction_norm`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.chiralScale_eq_zero_of_projectors_commute`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ConformalUnification.ConformalInference`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.chiralScale_ne_zero_of_projectors_not_commute`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ConformalUnification.ConformalInference`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.einsteinEquation_of_projectorObstruction_source`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ConformalUnification.ConformalInference`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.isChiralInference_iff_epsilon_pos`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.isNormalInference_iff_epsilon_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.isNormalInference_of_kahlerLogDet_unitRelativeVolume`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ConformalUnification.ConformalInference`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.isNormalInference_of_logDetBarrier_selfConcordance_mechanics`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ConformalUnification.ConformalInference`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.projectors_commute_of_chiralScale_eq_zero`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.ConformalUnification.ConformalInference`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.projectors_commute_of_kahlerLogDet_normalized_fixedpoint`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.ChiralEinsteinBridge.SatisfiesAnomalyDrivenScalarRicciFlow`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.unitOfAction_eq_chiralScale`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.ConformalUnification.ConformalInference.actionStructureConstantOp`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.unitOfAction_eq_zero_of_normalInference`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ConformalUnification.ConformalInference`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.unitOfAction_pos_of_chiralInference`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ConformalUnification.ConformalInference`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.unitOfAction_pos_of_noncommute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ConformalProjectorCore.lean`

- **`InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.metricProjector_idempotent`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.metricProjector_star`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.CertifiedInverseKernel.metricProjector_star`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.mpRangeProjector_idempotent`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.mpRangeProjector_star`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.spectralProjector_idempotent`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.spectralProjector`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.chiralAnomalyOperator_eq_zero_iff_projectors_commute`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.ConformalUnification.ConformalInference`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.chiralAnomaly_eq_zero_of_projectors_commute`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.ConformalUnification.ConformalInference`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.einsteinAnomaly_eq_neg_chiralAnomaly_of_projectorAgreement`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ConformalUnification.ConformalInference`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.projectors_commute_of_chiralAnomaly_eq_zero`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.ConformalUnification.ConformalInference`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.specialConformal_eq_modularInversion_translation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.spectralProjector_commutator_dilation_eq_half_sub_anomaly`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.ConformalUnification.ConformalInference`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.spectralProjector_commutator_dilation_eq_half_sub_mp_projector_commutators`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.ConformalUnification.ConformalInference`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.spectralProjector_commutator_dilation_eq_neg_half_einstein_plus_chiral`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.translation_eq_modularInversion_specialConformal`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ConnesArakiCore.lean`

- **`InfoGeometry.Canonical.ConnesArakiFramework.ArakiRelativeEntropyRestrictionDropMonotone.drop_abs_le`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConnesArakiFramework.abs_squeezingLogShear_le_of_abs_time_le_arakiRelativeEntropyDrop`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.MongeAmpereCramerRao.squeezingLogShear`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/ConnesArakiTomita.lean`

- **`InfoGeometry.Canonical.ConnesArakiFramework.abs_squeezingLogShear_le_of_abs_time_le_tomitaArakiRelativeEntropyDrop`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ConnesArakiFramework.TomitaConnesArakiData`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ConnesArakiFramework.topologicalBekensteinBound_and_tomitaModularKMS_of_tomitaConnesArakiData`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/CountPositiveCoupling.lean`

- **`InfoGeometry.Canonical.CountSubstrateBridge.countInducedCoupling_entrywisePositive`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.CountSubstrateBridge.CountSubstrate`
  - Tags: `statement-bearing`, `wrapper-candidate`
- **`InfoGeometry.Canonical.CountSubstrateBridge.countInducedPositiveIterate.colNormalize_entrywisePositive`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CountSubstrateBridge.countInducedPositiveIterate.rowNormalize_entrywisePositive`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/CountProbabilityState.lean`

- **`InfoGeometry.Canonical.CountSubstrateBridge.empiricalProbabilityState_spec`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/CountSinkhornFlow.lean`

- **`InfoGeometry.Canonical.CountSubstrateBridge.emergentTimeFlow_countInducedSinkhornTrajectory`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.CountSubstrateBridge.CountSubstrate`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/Determinant.lean`

- **`InfoGeometry.Canonical.Determinant.linearEquivLogGenerator_eq_logAbsVolume`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Determinant.linearEquivLogGenerator_mul`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ExactDescentLogGenerator.map_mul`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/DeterminantCore.lean`

- **`InfoGeometry.Canonical.Determinant.jac_det_comp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Determinant.logAbsDet_mul`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Determinant.range_toGL_eq_preimage_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/DiagonalMetricModularBridge.lean`

- **`InfoGeometry.Canonical.DiagonalMetricModularBridge.countDiagonalHessianGeometryOfRelativeCountDensitySumBound_metricOp_eq_countModularHamiltonian`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DiagonalMetricModularBridge.countDiagonalHessianGeometryOfRelativeCountDensitySumBound_metricOp_eq_relativeTomitaTakesakiOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DiagonalMetricModularBridge.countDiagonalScalar_nonneg_of_relativeCountDensity_sum_le_card`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.DiagonalMetricModularBridge.countDiagonalScalar`
  - Tags: `statement-bearing`, `wrapper-candidate`
- **`InfoGeometry.Canonical.DiagonalMetricModularBridge.spectral_dirac_sq_apply_eq_relativeModularHamiltonian_smul_of_isDiagonalRelativeCountMetricSlice`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DiagonalMetricModularBridge.spectral_dirac_sq_eq_countModularHamiltonian_of_isDiagonalRelativeCountMetricSlice`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/DiracMetricCompatibility.lean`

- **`InfoGeometry.Canonical.DiracMetricCompatibility.canonicalDiracOfMetric_isPositive`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/Drazin.lean`

- **`InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection_is_idempotent`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection_mul_projection`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.Drazin.IsDrazinInverse.fitting_decomposition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Drazin.IsDrazinInverse.inverse_eq_pow_mul_pow`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Drazin.IsDrazinInverse.nilpotent_comm_self`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.Drazin.IsDrazinInverse.nilpotent`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.Drazin.IsDrazinInverse.power_le`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.Drazin.IsDrazinInverse.power`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection_add_complementaryProjection`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection_comm`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection_is_idempotent`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.Drazin.IsDrazinInverse.idempotent`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection_mul_complementaryProjection`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/DualConnectionsCore.lean`

- **`InfoGeometry.Canonical.DualConnections.alphaConnection.deformation_law`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DualConnections.alphaConnection.dual_undual`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DualConnections.alphaConnection.undual_dual`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DualConnections.alphaConnectionTensor_dual_diff`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DualConnections.alphaConnectionTensor_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DualConnections.chentsovTensor_swap_left`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DualConnections.e_m_connection_sum`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.DualConnections.alphaConnectionTensor_dual_sum`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.DualConnections.fisherBilinear_comm`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DualConnections.fisherBilinear_self_nonneg`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DualConnections.fisherMetric_of_finProb`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DualConnections.fisher_metric_eq_hessian_KL`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.DualConnections.fisherMetric`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/DualConnectionsFiniteExpFamily.lean`

- **`InfoGeometry.Canonical.DualConnections.finiteExpFamilyAlphaConnection_deformation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DualConnections.finiteExpFamilyProbMap_apply_toReal`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DualConnections.fisherMetric_eq_covariance`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DualConnections.fisherQuadratic_eq_fisherBilinear_centeredScore`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/EmpiricalChecks.lean`

- **`InfoGeometry.Canonical.EmpiricalChecks.switch_selectedRoutingEpsilon_le_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.EmpiricalChecks.twoState_freeEnergy_identity`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Thermo.freeEnergy_eq_internal_sub_scale_entropy`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.EmpiricalChecks.twoState_freeEnergy_identity_unit`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Thermo.freeEnergy`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.EmpiricalChecks.twoState_gibbs_sum_one`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Thermo.gibbsProb_sum_one`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.EmpiricalChecks.twoState_partition_pos`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.EmpiricalChecks.twoStateEnergy`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/Fock.lean`

- **`InfoGeometry.Canonical.Fock.bayesianUpdate_eq_creationExcitation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Fock.dataPart_eq_creation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Fock.modelPart_eq_annihilation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/FormalScaffold.lean`

- **`InfoGeometry.Canonical.Bregman.pythagorean_law`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Geometry.DualFlat.DualFlatStructure`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/GaugeGroups.lean`

- **`InfoGeometry.Canonical.GaugeGroups.PSUN.is_quotient`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GaugeGroups.SUN.is_special`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GaugeGroups.SUN.is_unitary`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GaugeGroups.SUNCenter.cardinality`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GaugeGroups.SUNCenter.is_roots_of_unity`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/GaugeUnified.lean`

- **`InfoGeometry.Canonical.Gauge.act_preserves_bilinear`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/GaussianHolonomy.lean`

- **`InfoGeometry.Canonical.GaussianHolonomy.gaussianDiracField_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GaussianHolonomy.gaussianDiracField_const`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/GeneratedFlow.lean`

- **`InfoGeometry.Canonical.GeneratedFlow.along_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GeometricResponse.along_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GeometricResponse.fromLogGenerator_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GeometricResponse.fromLogGenerator_eq_along_comp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.LogGenerator.generate_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.LogGenerator.generate_eq_along`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.LogGenerator.respond_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.LogGenerator.respond_eq_fromLogGenerator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.LogGenerator.respond_eq_responseOf_comp_generate`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/GrandCanonicalExperts.lean`

- **`InfoGeometry.Canonical.MoE.cliffordBasis_minus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.cliffordBasis_plus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.diracAction_def`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.diracEulerStep_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.exists_clifford_labeled_state_of_bistochastic`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.exists_modewiseClifford_rep_of_bistochastic`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.labelGenerator_sq`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.MoE.cliffordBasis`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.labelGenerator_sq_minus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.labelGenerator_sq_plus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.modeDiracAction_respects_grading`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.modewiseCliffordState_split`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.MoE.PermutationMode`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.parity_minus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.parity_plus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.splitB11_splitBasis_orthogonal`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.splitQ11_splitBasisMinus`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.MoE.splitBasisMinus`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.splitQ11_splitBasisPlus`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.MoE.splitBasisPlus`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.splitSuperBracket_minus_minus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.splitSuperBracket_plus_left`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.splitSuperBracket_plus_right`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.superSign_minus_minus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.superSign_plus_left`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.superSign_plus_right`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/GrandSynthesisBott.lean`

- **`InfoGeometry.Canonical.GrandSynthesis.cl11_bottDirac_sq_eq_zero_of_lichnerowiczBalanced`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.SpectralInference.InfoSpectralTriple.x₀`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/GrandSynthesisGeometry.lean`

- **`InfoGeometry.Canonical.GrandSynthesis.logAbsDetMatrix_kronecker`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GrandSynthesis.logAbsDetMatrix_mul`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GrandSynthesis.logAbsJacDetCLM_comp`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.GrandSynthesis.jacDetCLM`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.GrandSynthesis.log_spectralMongeAmpereDensity_eq_basepointLogVolume`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.SpectralInference.InfoSpectralTriple.x₀`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/GrandSynthesisSingular.lean`

- **`InfoGeometry.Canonical.GrandSynthesis.regularRadialTransportCloses_of_boundaryGenerator_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/GrandSynthesisThermo.lean`

- **`InfoGeometry.Canonical.GrandSynthesis.doublyStochastic_sinkhornEntropyMonotoneRN`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ChiralAnomaly.DoublyStochasticSinkhornTrajectory`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.GrandSynthesis.ricci_component_constant_of_geometricEquilibrium`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.RicciMongeAmpere.RicciFlow`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.GrandSynthesis.sinkhornEntropyMonotoneRN`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.MoE.trajectoryRNBarrier_monotone`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.GrandSynthesis.thermodynamicEquilibrium_of_doublyStochastic`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ChiralAnomaly.sinkhorn_dynamics_step_control`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/GrandUnification.lean`

- **`InfoGeometry.Canonical.GrandUnification.JordanKKTData.detJ_pos`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GrandUnification.JordanKKTData.dualPotential_grad_eq`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.GrandUnification.JordanKKTData.dualPotential`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.GrandUnification.JordanKKTData.dual_potential_mixed_identity`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GrandUnification.JordanKKTData.fenchel_young_equality`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.GrandUnification.JordanKKTData.detJ`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.GrandUnification.JordanKKTData.generalized_pythagorean_theorem`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.GrandUnification.JordanKKTData.DBregman`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.GrandUnification.JordanKKTData.hasFDerivAt_K`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.GrandUnification.JordanKKTData`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.GrandUnification.JordanKKTData.mixed_bregman_identity`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.GrandUnification.JordanKKTData.dualPotential`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.GrandUnification.JordanKKTData.projection_minimizes`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GrandUnification.JordanKKTData.projection_unique`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GrandUnification.JordanKKTData.pythagorean_inequality`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.GrandUnification.JordanKKTData.DBregman`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.GrandUnification.JordanKKTData.three_point_law`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.GrandUnification.JordanKKTData.DBregman.eq_1`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/GrandUnificationMetric.lean`

- **`InfoGeometry.Canonical.GrandUnification.JordanKKTData.bregman_local_second_order_of_logDet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GrandUnification.JordanKKTData.metric_nonneg_of_metricPositive`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GrandUnification.JordanKKTData.metric_symmetry_of_metricPositive`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/HeatKernel.lean`

- **`InfoGeometry.Canonical.HeatKernel.a0_eq_spectralLogVolume`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.HeatKernel.einsteinHilbertAction_eq_totalScalarCurvature`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.HeatKernel.spectralLogVolume_eq_spectralBasepointLogVolume`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.HeatKernel.totalScalarCurvature_eq_neg_six_spectralLogVolume`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.HeatKernel.totalScalarCurvature_eq_spinorialScalarCurvature`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/IBBase.lean`

- **`InfoGeometry.Canonical.IB.FrozenFiniteRegime.ofReal_toReal_fin_kl_div_cond`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.IB.condYGivenX`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.FrozenFiniteRegime.ofReal_toReal_fin_kl_div_encoder`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.IB.FrozenFiniteRegime`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.baScoreFrozen_ne_top`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.IB.IBProblem.beta`
  - Tags: `high-fan-in`, `statement-bearing`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.baScoreFrozen_slice_ne_top`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.IB.baScoreFrozen`
  - Tags: `high-fan-in`, `statement-bearing`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.baScoreFrozen_slice_toReal_pos`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/IBCanonical.lean`

- **`InfoGeometry.Canonical.IB.baStep_encoderMassNndist_le`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.baStep_eq_of_scoreRay_eq`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.IB.ibBlahutArimotoStep_eq_of_scoreRay_eq`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.baStep_eq_scoreRay_gaugeSection`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.IB.ibBlahutArimotoStep_eq_scoreRayGaugeSection`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.baStep_pointwise_massNndist_le`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.baStep_radial_projective_split`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.IB.ibBlahutArimotoStepUnnormalized`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.frozenFreeEnergy_eq_gap_minus_logPartition`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.IB.ibFrozenFreeEnergy_eq_gap_minus_logPartition`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.frozenVariational_descent`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.IB.ibVariationalFunctional_frozen_descent`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/IBFiniteIteration.lean`

- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStep_variational_descent_currentTarget`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.IB.ibVariationalFunctionalFrozen`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.ibTrajectory_step_descent_frozenTarget`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibTrajectory_step_gap_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibTrajectory_variational_descent_currentTarget`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/IBFiniteMonotonicity.lean`

- **`InfoGeometry.Canonical.IBFiniteMonotonicity.IBNextEncoder_positive_of_fullSupport`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.IBFinitePythagorean.IBNextEncoder_positive_of_ref_positive`
  - Tags: `statement-bearing`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IBFiniteMonotonicity.IB_monotone_descent_finite_fullSupport`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IBFiniteMonotonicity.encoderDescent_finite_fullSupport`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IBFiniteMonotonicity.finiteSliceJaynes_fullSupportPrior`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.MeasureProjective.Normalized.probMeasureToPMF`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IBFiniteMonotonicity.finiteSliceObjective_eq_kl_to_next_minus_logPartition`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.IBFiniteMonotonicity.finiteSliceObjective_eq_kl_to_next_minus_logPartition_of_supportFaithful`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IBFiniteMonotonicity.finiteSliceObjective_minimized_by_IBNextEncoder`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.MeasureProjective.Normalized.probMeasureToPMF`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IBFiniteMonotonicity.ibDescentWitness_finite_fullSupport`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/IBFinitePythagorean.lean`

- **`InfoGeometry.Canonical.IBFinitePythagorean.IBNextEncoder_supportFaithful_ref`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.IBFinitePythagorean.ref_positive_of_IBNextEncoder_positive`
  - Tags: `high-fan-in`, `statement-bearing`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IBFinitePythagorean.IBNextMarginal_positive_of_encoder_positive`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.IBPythagorean.IBNextEncoder`
  - Tags: `statement-bearing`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IBFinitePythagorean.finiteWeightedKL_bind_marginal_decomposition_fullSupport`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.IBFinitePythagorean.finiteWeightedKL_bind_marginal_decomposition`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IBFinitePythagorean.ibMarginalDescentWitness_finite_fullSupport`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IBFinitePythagorean.integral_exp_neg_distortion_pos`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.MeasureProjective.Normalized.probMeasureToPMF`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IBFinitePythagorean.klDiv_eq_fin_klDiv_toReal`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.KL.kl_div`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IBFinitePythagorean.pmf_bind_supportFaithful_ref`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.IBFinitePythagorean.pmf_bind_apply_toReal`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IBFinitePythagorean.probMeasureToPMF_IBNextEncoder_toReal`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.IBPythagorean.IBNextEncoder`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IBFinitePythagorean.probMeasureToPMF_toMeasure`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.MeasureProjective.Normalized.probMeasureToPMF`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/IBFreeEnergy.lean`

- **`InfoGeometry.Canonical.IBFreeEnergy.klDivENN_self`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/IBFrozenDescent.lean`

- **`InfoGeometry.Canonical.IB.baFrozenTargetGap_eq_baFrozenTargetGapWith_induced`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStepFrozen_descent_frozenTargetGap`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibFrozenFreeEnergy_hPDecomp`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.IB.ibFrozenFreeEnergy_eq_gap_minus_logPartition`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.ibFrozenFreeEnergy_hStepDecomp`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.IB.ibFrozenFreeEnergy_eq_gap_minus_logPartition`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.ibVariationalFunctionalLoose_eq_sum_local`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibVariationalFunctional_frozen_descent`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.IB.ibVariationalFunctionalFrozen`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.ibVariationalFunctional_frozen_descent_of_gap_decomposition`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.IB.ibVariationalFunctionalFrozen`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.ibVariationalFunctional_le_loose`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.IB.IBProblem.beta`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/IBFrozenJaynes.lean`

- **`InfoGeometry.Canonical.IB.frozenSliceJaynes_partition_one_ne_zero`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.IB.IBProblem.beta`
  - Tags: `statement-bearing`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.frozenSlice_logPartition_eq_logPartitionFrozen`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.IB.frozenSlice_partition_eq_baScoreFrozen_tsum_toReal`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.frozenSlice_partition_eq_baScoreFrozen_tsum_toReal`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.IB.IBProblem.beta`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/IBFrozenModularBridge.lean`

- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStepFrozen_scalarModularPotential_sub_logPartitionFrozen_eq_betaKL`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.IB.IBProblem.beta`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/IBFunctional.lean`

- **`InfoGeometry.Canonical.IBFunctional.IBMarginalize_congr`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IBFunctional.bindEncoderMeasure_univ`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/IBGaugeBridge.lean`

- **`InfoGeometry.Canonical.IBGaugeBridge.IBGibbsMeasure_shift_eq`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.IBGaugeBridge.distortionShift`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IBGaugeBridge.IBPartitionFunction_shift_eq_smul`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.IBGaugeBridge.distortionShift`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IBGaugeBridge.IBUnnormalized_shift_ne_zero`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.IBGaugeBridge.distortionShift`
  - Tags: `statement-bearing`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IBGaugeBridge.ibProjectiveState_eq_of_shift`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IBGaugeBridge.ibProjectiveState_normalize_eq_IBGibbs`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/IBIteration.lean`

- **`InfoGeometry.Canonical.IBIteration.IBKernel_isMarkovKernel`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IBIteration.IBStepMeasure_eq_comp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/IBMeasure.lean`

- **`InfoGeometry.Canonical.IBMeasure.IBNormalize_toMeasure_eq_inv_mass_smul_of_nonzero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IBMeasure.IBPartitionFunction_eq_lintegral`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.IBMeasure.IBPartitionFunction`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IBMeasure.partitionFunction_eq_lintegral`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.IBMeasure.partitionFunction`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IBMeasure.rnDeriv_IBGibbs_eq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IBMeasure.rnDeriv_IBUnnormalized_eq`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.IBMeasure.rnDeriv_tiltedMeasure`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/IBMonotonicity.lean`

- **`InfoGeometry.Canonical.IBMonotonicity.IB_monotone_descent`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.IBPythagorean.IBNextMarginalDescentWitness`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/IBNormalize.lean`

- **`InfoGeometry.Canonical.IB.baScoreFrozenMeasure_normalize_eq_stepFrozen`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.baScoreMeasure_normalize_eq_step`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/IBProjective.lean`

- **`InfoGeometry.Canonical.IB.FullSupportScoreRay.positiveRay_mk`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.FullSupportScoreSlice.pointwise_finite`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.FullSupportScoreSlice.pointwise_nonzero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.FullSupportScoreSlice.sameRay_toPositiveMeasure`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.IB.FullSupportScoreSlice.toPositiveMeasure`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.FullSupportScoreSlice.toPositiveMeasure_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.SameScoreRay.refl`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`, `rfl-like`
- **`InfoGeometry.Canonical.IB.SameScoreRay.symm`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.SameScoreRay.trans`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ScoreRay.gaugeSection_mk`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ScoreRay.normalize_projectiveState`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.IB.ScoreRay`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.ScoreRay.normalize_toProjectiveState`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.IB.ScoreRay.toProjectiveState`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.ScoreRay.projectiveState_mk`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.pmf_normalize_apply_toReal`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`, `rfl-like`
- **`InfoGeometry.Canonical.IB.pmf_normalize_eq_of_sameScoreRay`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.IB.pmf_normalize_eq_of_scale`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.pmf_normalize_eq_self`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.scoreProjectiveGauge_eq_of_sameScoreRay`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.IB.pmf_normalize_eq_of_sameScoreRay`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/IBPythagorean.lean`

- **`InfoGeometry.Canonical.IBPythagorean.IBMarginalize_eq_encoderKernel_comp`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.IBPythagorean.encoderKernel`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IBPythagorean.IB_marginal_descent_of_pythagorean`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IBPythagorean.IB_marginal_descent_of_witness`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.IBFunctional.FiniteKLFamily`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IBPythagorean.IB_next_marginal_descent_of_pythagorean`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IBPythagorean.IB_next_marginal_descent_of_witness`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.IBPythagorean.IBNextMarginalDescentWitness`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IBPythagorean.encoderKernel_isMarkovKernel`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IBPythagorean.ibMarginalPythagoreanWitness_of_marginalization`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.IBFunctional.FiniteKLFamily`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IBPythagorean.ibMarginalPythagorean_identity_of_marginalization`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.IBPythagorean.IBMarginalize_eq_encoderKernel_comp`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IBPythagorean.ibNextMarginalPythagoreanWitness_of_marginalization`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.IBFunctional.FiniteKLFamily`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/IBTilted.lean`

- **`InfoGeometry.Canonical.IB.baFrozenTilted_apply_singleton`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.IB.frozenPotential`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.baScoreFrozenMeasure_toMeasure_eq_priorWithDensity`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.frozenWeight_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.integrable_exp_frozenPotential`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/IBTopological.lean`

- **`InfoGeometry.Canonical.IBTopological.F_deriv_eq_neg_gibbsExpectation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IBTopological.F_secondDeriv_eq_variance`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/IBTrajectory.lean`

- **`InfoGeometry.Canonical.IB.exists_ibTrajectory`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibTrajectory_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.tendsto_ibTrajectory_fixedPoint`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.IB.IBProblem`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.tendsto_ibTrajectory_fixedPoint_of_lipschitz`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/IBUnnormalized.lean`

- **`InfoGeometry.Canonical.IB.baScoreFrozenMeasure_apply_singleton`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.baScoreFrozenMeasure_ne_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.baScoreMeasure_apply_singleton`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.baScoreMeasure_ne_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.discreteScoreMeasure_apply_singleton`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.IB.discreteScoreMeasure`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.discreteScoreMeasure_ne_zero_of_tsum_ne_zero`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.IB.ennreal_discreteScoreMeasure_mass`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.ennreal_baScoreFrozenMeasure_mass`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ennreal_baScoreMeasure_mass`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ennreal_discreteScoreMeasure_mass`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.IB.discreteScoreMeasure`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/IBUpdate.lean`

- **`InfoGeometry.Canonical.IB.baNormalize_pointwise_massNndist_le_of_massRecipLipschitz_intrinsicUpper`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.IB.baNormalize_pointwise_massNndist_le_of_massRecipLipschitz`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.baNormalize_pointwise_massNndist_le_zero_of_sameScoreRay`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.IB.pmf_normalize_eq_of_sameScoreRay`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.baScore_eq_baScoreFrozen_induced`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.finProbMassNndist_eval_le_encoderMassNndist`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoProjectiveState_eq_of_sameScoreRay`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.IB.ibBlahutArimotoScoreRay_eq_of_sameScoreRay`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoProjectiveState_eq_of_scoreRay_eq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoProjectiveState_eq_of_score_ray_scale`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.IB.ibBlahutArimotoStep_eq_of_score_ray_scale`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStepFrozen_eq_of_score_ray_scale`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStepFrozen_eq_prior_of_uniformDistortion`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStep_dilation_split`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStep_encoderMassNndist_le_of_massRecipLipschitz`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStep_encoderMassNndist_le_of_normalize_intrinsicNonzero`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.IB.baScore`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStep_encoderMassNndist_le_zero_of_sameScoreRay`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStep_encoderMassNndist_le_zero_of_scoreRay_eq`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.IB.ScoreRay`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStep_encoderNndist_le_of_pointwise`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStep_eq_frozen_induced`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStep_eq_of_sameScoreRay`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStep_eq_of_scoreRay_eq`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.IB.ScoreRay`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStep_eq_scoreProjectiveGauge`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.IB.ibBlahutArimotoStepUnnormalized`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStep_pointwise_massNndist_le_of_massRecipLipschitz_intrinsicUpper`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.IB.baScore`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStep_pointwise_massNndist_le_of_normalize`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.IB.baScore`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStep_pointwise_massNndist_le_of_normalize_intrinsicNonzero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStep_pointwise_massNndist_le_zero_of_scoreRay_eq`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.IB.ibBlahutArimotoStep_eq_of_scoreRay_eq`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStep_slice_eq_of_sameScoreRay`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.nndist_eval_le_encoderNndist`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.nndist_eval_le_finProbMassNndist`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/InformationNumber.lean`

- **`InfoGeometry.Canonical.InformationNumber.exists_natCast_eq_informationNumber`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.InformationNumber.informationNumber_eq_ambientDim_of_surjectiveProjection`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.InformationNumber.informationNumber_le_ambientDim`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.InformationNumber.informationNumber_nonneg`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/InformationPartitionCore.lean`

- **`InfoGeometry.Canonical.InformationCalculus.ModularRadonNikodymData.deriv_informationPartitionFunction_zero`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.InformationCalculus.ModularRadonNikodymData.informationPartitionFunction`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.InformationCalculus.ModularRadonNikodymData.hasDerivAt_informationPartitionFunction_zero_modularHamiltonian`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.InformationCalculus.ModularRadonNikodymData.hasDerivAt_logInformationPartitionFunction_zero_modularHamiltonian_of_normalized`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.InformationCalculus.ModularRadonNikodymData.hasDerivAt_logInformationPartitionFunction_zero_of_normalized`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.InformationCalculus.ModularRadonNikodymData.informationPartitionFunction_one`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.InformationCalculus.ModularRadonNikodymData.informationPartitionFunction`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.InformationCalculus.ModularRadonNikodymData.informationPartitionFunction_zero`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.InformationCalculus.ModularRadonNikodymData.informationPartitionFunction`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.InformationCalculus.ModularRadonNikodymData.instCompleteSpaceEndH`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.YangMillsContinuum.EndH`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/InformationTorsion.lean`

- **`InfoGeometry.Canonical.InformationTorsion.FlatDualConnections.torsion_free_nabla`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.InformationTorsion.FlatDualConnections.torsion_free_nablaStar`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/JaynesRNMaxEnt.lean`

- **`InfoGeometry.Canonical.JaynesRNMaxEnt.objectiveKL_def`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/JaynesRNModularBridge.lean`

- **`InfoGeometry.Canonical.JaynesRNMaxEnt.neg_log_rnDeriv_gibbsMeasure_toReal_eq_neg_potential_add_logPartition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.JaynesRNMaxEnt.potential_eq_log_rnDeriv_gibbsMeasure_toReal_add_logPartition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.JaynesRNMaxEnt.scalarModularPotential_exp_potential_div_partition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/KLinearRepresentation.lean`

- **`InfoGeometry.Canonical.KLinearRepresentation.J_isKAntilinear`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KLinearRepresentation.K_isKLinear`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KLinearRepresentation.PolarizedDecomposition.h_anti`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KLinearRepresentation.PolarizedDecomposition.h_lin`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KLinearRepresentation.PolarizedDecomposition.h_sum`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KLinearRepresentation.eps_isKAntilinear`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KLinearRepresentation.id_isKLinear`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KLinearRepresentation.kLinearPart_add_kAntilinearPart`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KLinearRepresentation.neg_K_comp_kConjugate`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KLinearRepresentation.neg_kConjugate_comp_K`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/KMSSinkhornScalarPotential.lean`

- **`InfoGeometry.Canonical.KMSSinkhornBridge.exp_neg_jacobianLogPotential_eq_jacobianRelativeVolume`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.KMSSinkhornBridge.jacobianRelativeVolume`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.KMSSinkhornBridge.ibRNPotential_eq_jacobianLogPotential_of_relativeVolume_match`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.KMSSinkhornBridge.jacobianRelativeVolume`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.KMSSinkhornBridge.ibRNPotential_eq_neg_log_relativeVolumeChange`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.KMSSinkhornBridge.ibRNDerivative`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.KMSSinkhornBridge.ibRNPotential_eq_scalarModularPotential_relativeVolumeChange`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KMSSinkhornBridge.ibRelativeVolumeChange_eq_ibRNDerivative`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.KMSSinkhornBridge.ibObservableWeight`
  - Tags: `statement-bearing`, `wrapper-candidate`
- **`InfoGeometry.Canonical.KMSSinkhornBridge.jacobianLogPotential_eq_scalarModularPotential`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/KMSSinkhornSeedState.lean`

- **`InfoGeometry.Canonical.KMSSinkhornBridge.expectationSeedFunctional_id`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.KMSSinkhornBridge.expectationSeedFunctional_kms_of_structural`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.KMSSinkhornBridge.omegaSeed_apply`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.KMSSinkhornBridge.omegaSeed_nonzero_of_thermalVacuum`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/KMSSinkhornWeightedTransport.lean`

- **`InfoGeometry.Canonical.KMSSinkhornBridge.ibInducedObservableWeighted_nonzero`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.KMSSinkhornBridge.ibInducedObservableWeighted`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.KMSSinkhornBridge.ibRNPotentialBarrierBudget_pos`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KMSSinkhornBridge.ibRNPotential_approxKMSClosure_of_ibDynamics_weighted`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KMSSinkhornBridge.ibRNPotential_approxKMSClosure_of_ibDynamics_weighted_from_jointKernel_commutator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KMSSinkhornBridge.ibRNPotential_kmsControl_of_ibDynamics_weighted`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/KaehlerGeometry.lean`

- **`InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry.compatibility`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry.j_sq_eq_neg_id`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry.logF_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry.logF_eq_potential`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/KreinDiracPolarizationBridge.lean`

- **`InfoGeometry.Canonical.KreinDiracPolarizationBridge.doubledKreinDiracPolarizationBridge_of_strictSymmetry`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KreinDiracPolarizationBridge.kreinDiracPolarizationBridge_of_strictSymmetry`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KreinDiracPolarizationBridge.transportDirac_sq_eq_transportMetricOp_of_strictSymmetry`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Quantum.RealMajorana.PolarizedMajorana`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.KreinDiracPolarizationBridge.transportEnd_id`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.RealMajorana.RealBogoliubovTransform.B`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/KreinDiracSpectralLift.lean`

- **`InfoGeometry.Canonical.KreinDiracSpectralLift.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.KreinDiracSpectralLift.kreinDiracSpectralLift_of_strictSymmetry`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KreinDiracSpectralLift.transportDiracFlow_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/KreinDiracWeightFunctionalLift.lean`

- **`InfoGeometry.Canonical.KreinDiracWeightFunctionalLift.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.KreinDiracWeightFunctionalLift.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KreinDiracWeightFunctionalLift.transportDiracFlow_add_of_strictSymmetry`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KreinDiracWeightFunctionalLift.transportedThermalFlow_add_of_strictSymmetry`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/KreinDoubledAtom.lean`

- **`InfoGeometry.Canonical.KreinDoubledAtom.Atom.eps_sq`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.KreinDoubledAtom.Atom`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.KreinDoubledAtom.Atom.j_eps_anticomm`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.KreinDoubledAtom.Atom`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.KreinDoubledAtom.Atom.j_sq`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.KreinDoubledAtom.Atom`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.KreinDoubledAtom.Atom.k_eq_j_comp_eps`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.KreinDoubledAtom.Atom`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.KreinDoubledAtom.Atom.k_sq`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.KreinDoubledAtom.Atom`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.KreinDoubledAtom.Core.eps_sq`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.KreinDoubledAtom.Core`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.KreinDoubledAtom.Core.j_eps_anticomm`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.KreinDoubledAtom.Core`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.KreinDoubledAtom.Core.j_sq`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.RealMajoranaCategory.RealMajoranaCore.J_sq`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.KreinDoubledAtom.Core.k_eq_j_comp_eps`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KreinDoubledAtom.Core.k_sq`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.KreinDoubledAtom.Core`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.KreinDoubledAtom.Core.pi_sq`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.KreinDoubledAtom.Core`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.KreinDoubledAtom.J_eps_anti`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Quantum.AnticommutingInvolutionCore.J_eps_anticomm`
  - Tags: `high-fan-in`, `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.KreinDoubledAtom.J_sq`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.AnticommutingInvolutionCore.toInvolutionCore`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.KreinDoubledAtom.K_eq_J_comp_eps`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.KreinDoubledAtom`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.KreinDoubledAtom.K_sq_eq_neg_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KreinDoubledAtom.eps_comp_J`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.AnticommutingInvolutionCore.eps_comp_J`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.KreinDoubledAtom.eps_sq`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.AnticommutingInvolutionCore.toInvolutionCore`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/KreinLadder.lean`

- **`InfoGeometry.Canonical.KreinLadder.InformationLadder.a_persistent`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/LLNCore.lean`

- **`InfoGeometry.Canonical.LLN.ae_tendsto_ratio_to_rnDeriv_holds`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`, `rfl-like`
- **`InfoGeometry.Canonical.LLN.fixed_partition_slln_holds`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/LogGenerator.lean`

- **`InfoGeometry.Canonical.DefectiveDescentLogGenerator.map_mul_defect`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.DefectiveDescentLogGenerator`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ExactDescentLogGenerator.map_mul`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.ExactMultiplicativeToAdditiveBridge.additiveInvariant_mul`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.OperatorLogGenerator.map_mul_of_commute`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.OperatorLogGenerator`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/LogSpineBridge.lean`

- **`InfoGeometry.Canonical.LogSpine.jordan_logdet_eq_zeta_determinant`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.Determinant.zetaLogDetBarrier_eq_logDetBarrier`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.LogSpine.kahler_spine_entropy_identity`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/LogSumExp.lean`

- **`InfoGeometry.Canonical.LogSumExp.logSumExp_eq_log_partition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/LorentzianRouting.lean`

- **`InfoGeometry.Canonical.Attention.timelike_dominance`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ManifoldDegreeCore.lean`

- **`InfoGeometry.Canonical.ManifoldDegree.exists_isolating_nhds_of_discrete`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`, `rfl-like`
- **`InfoGeometry.Canonical.ManifoldDegree.regularValue_of_nonvanishing_jacobian`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`, `rfl-like`

### `lean/InfoGeometry/Canonical/ManifoldHomologyCore.lean`

- **`InfoGeometry.Canonical.ManifoldHomology.mappingDegree_eq_sum_localDegreeSign`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/MixtureOfExperts.lean`

- **`InfoGeometry.Canonical.MoE.mixture_gauge_reduction`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.normalizedWeights_sum_one`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.MoE.routerPartition`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/ModularSpinorBridge.lean`

- **`InfoGeometry.Canonical.ModularSpinorBridge.MajoranaFrame.is_cl11`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularSpinorBridge.bayesian_update_as_spinor_bilinear`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.KreinSpace.jCLM`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ModularSpinorBridge.bayesian_update_as_spinor_bilinear_witness`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.KreinSpace.jCLM`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ModularSpinorBridge.fierzIdentity_true`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularSpinorBridge.modularFlowInducedTransport_eq_id_of_flow_id`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularSpinorBridge.modularSpinConnection_transport`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularSpinorBridge.transportedSplitVielbein_modularSpinConnection`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularSpinorBridge.weakValueNumerator_modularConjugate_eq_spinorBilinear`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.HilbertDoubled`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ModularSpinorBridge.weakValue_modularConjugate_eq_spinorBilinear_div_overlap`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularSpinorBridge.weakValue_numerator_eq_spinorBilinear`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.HilbertDoubled`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/ModularVolumeDeformationBridge.lean`

- **`InfoGeometry.Canonical.ModularVolumeDeformationBridge.projective_logVolumeDeformation_eq_raw_add_massShift`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialCountBridge.relativeLogDensity_countRay_eq_relativeCountLogDensity_add_massShift`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ModularVolumeDeformationBridge.projective_logVolumeDeformation_eq_raw_sub_log_countRelativeVolumeChange`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialCountBridge.relativeLogDensity_countRay_eq_relativeCountLogDensity_sub_log_countRelativeVolumeChange`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ModularVolumeDeformationBridge.projective_modularPotential_eq_raw_sub_scalarModularPotential_relativeVolumeChange`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialCountBridge.relativeModularPotential_countRay_eq_relativeCountModularProfile_sub_scalarModularPotential_relativeVolumeChange`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ModularVolumeDeformationBridge.projective_relativeVolumeDeformation_eq_massRatio_mul_raw`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialCountBridge.relativeDensity_countRay_eq_massRatio_mul_relativeCountDensity`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.ModularVolumeDeformationBridge.scalar_modularPotential_is_neg_log`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialScalarBridge.scalarModularPotential_eq_neg_log`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/MongeAmpereCramerRao.lean`

- **`InfoGeometry.Canonical.MongeAmpereCramerRao.absDet_cramerRaoMetric_eq_one_of_incompressible`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereCramerRao.abs_squeezingLogShear_eq_four_mul_abs`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.MongeAmpereCramerRao.squeezingLogShear`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MongeAmpereCramerRao.abs_squeezingLogShear_le_of_abs_time_le_barrier`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.MongeAmpereCramerRao.squeezingLogShear`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MongeAmpereCramerRao.abs_squeezingLogShear_le_of_sinkhornTrajectory`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereCramerRao.abs_squeezingLogShear_le_of_topologicalBekensteinBound`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.MongeAmpereCramerRao.squeezingLogShear`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MongeAmpereCramerRao.logAbsDet_cramerRaoMetric_eq_zero_of_incompressible`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereCramerRao.squeezingEigen_product_eq_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/MongeAmpereDualSheetBridge.lean`

- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.dualSheetLift_apply_minusPoint`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.dualSheetLift_apply_plusPoint`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.snd_L`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.dualSheetLift_apply_to_doubled`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.dualSheetMongeAmpereConsistentAtBasepoint`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.SpectralInference.InfoSpectralTriple.x₀`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.minusBlockMap_dualSheetMetricOp`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Convex.HessianGeometry.metricOp`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.minusBlockMap_rnEntropyDualSheetSourceOp`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.MongeAmpereDualSheetBridge.minusPointL`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.minusBlockMap_squeezingTransport`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.minusPointL_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.minusProjectorFlux_dualSheetLift`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.minusProjectorFlux_dualSheetMetricOp`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.minusProjectorFlux_rnEntropyDualSheetSourceOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.minusProjectorFlux_squeezingTransport`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.minusToPlusBlockMap_dualSheetMetricOp`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.MongeAmpereDualSheetBridge.minusToPlusBlockMap`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.minusToPlusBlockMap_rnEntropyDualSheetSourceOp`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.MongeAmpereDualSheetBridge.minusPointL`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.minusToPlusBlockMap_squeezingTransport`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.MongeAmpereDualSheetBridge.minusPointL`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.mongeAmpereDensityOperator_eq_exp_metricLogDet_smul_id`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.mongeAmpereDensityOperator_eq_exp_neg_kahlerPotentialRN_smul_id_of_rnEntropySource`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.mongeAmpereDensityOperator_eq_exp_smul_id_of_satisfiesMongeAmperePotential`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.mongeAmpereDensityOperator_eq_id_of_incompressible`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.mongeAmpereDensityOperator_eq_rnEntropyDualSheetSourceOp_of_rnEntropySource`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.plusBlockMap_dualSheetMetricOp`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.MongeAmpereDualSheetBridge.plusBlockMap_dualSheetLift`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.plusBlockMap_rnEntropyDualSheetSourceOp`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.MongeAmpereDualSheetBridge.plusPointL`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.plusBlockMap_squeezingTransport`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.plusPointL_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.plusProjectorFlux_dualSheetLift`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.plusProjectorFlux_dualSheetMetricOp`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.plusProjectorFlux_rnEntropyDualSheetSourceOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.plusProjectorFlux_squeezingTransport`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.plusToMinusBlockMap_dualSheetMetricOp`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.MongeAmpereDualSheetBridge.plusToMinusBlockMap`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.plusToMinusBlockMap_rnEntropyDualSheetSourceOp`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.snd_L`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.plusToMinusBlockMap_squeezingTransport`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.snd_L`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.spectralMongeAmpereDensityOperator_eq_exp_spectralBasepointLogVolume_smul_id`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.SpectralInference.InfoSpectralTriple.x₀`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/MoorePenrose.lean`

- **`InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.leftProjector_idempotent`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.leftProjector`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.leftProjector_star`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.ba_star`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.mk`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`, `rfl-like`
- **`InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.rightProjector_idempotent`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.aba_eq_a`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.rightProjector_star`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.ab_star`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoorePenrose.chiralAnomaly_eq_zero_of_projectorMismatch_eq_zero`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.MoorePenrose.chiralAnomaly_eq_mismatch_commutator_metric`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoorePenrose.projectorMismatch_eq_zero_iff`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/MultiplicativeToAdditiveBridge.lean`

- **`InfoGeometry.Canonical.AdditiveLinearization.map_mul_apply`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.AdditiveLinearization.map_mul`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.DefectiveAbelianizingBridge.map_mul`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.DefectiveAbelianizingBridge`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.FunctionalCalculusLinearization.map_mul_of_commute_apply`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.FunctionalCalculusLinearization.map_mul_of_commute`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/NavierStokesBridge.lean`

- **`InfoGeometry.Canonical.FluidState.density_stationary`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.anomalyFluidStateWithDensity_rho`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.anomalyFluidStateWithDensity_u`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.anomaly_as_fluid_state`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.anomaly_as_fluid_state_with_density`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.chiral_anomaly_sources_flow`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.deriv_modularVelocity_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.hasDerivAt_modularVelocity_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.helicity_eq_twin_wave_pairing`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.madelungFluidState_velocity`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.madelungFluidState_zero_velocity`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.modular_circulation_response`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.vorticity_eq_self_of_skew`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/NoetherInference.lean`

- **`InfoGeometry.Canonical.NoetherInference.BayesianSymmetryOrbit.preserves_hessian`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.NoetherInference.BayesianSymmetryOrbit.update_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.NoetherInference.BayesianSymmetryOrbit.update_zero`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.NoetherInference.DSpace`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.NoetherInference.InformationKillingField.preserves_hessian`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.NoetherInference.InformationKillingField`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.NoetherInference.P_minus_conjugate_eq_of_theta_commutes`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.NoetherInference.DSpace`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.NoetherInference.evalAt_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.NoetherInference.fisherBilinAt_apply`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.NoetherInference.DSpace`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.NoetherInference.fisherBilinAt_conjugate_eq`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.NoetherInference.DSpace`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.NoetherInference.fisher_metric_eq_killing_form_of_orbit_base_relation`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.NoetherInference.DSpace`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.NoetherInference.fisher_metric_eq_killing_form_of_orbit_base_relation_and_killing_conjugation_invariance`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.NoetherInference.DSpace`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.NoetherInference.fisher_metric_eq_killing_form_of_orbit_base_relation_of_commutes_with_involution`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/OperatorAlgebraAQFTPackage.lean`

- **`InfoGeometry.Canonical.OperatorAlgebraBridge.cstar_completeCStar_kms_fock_projectorSuperPair_base_package`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OperatorAlgebraBridge.cstar_completeCStar_kms_fock_tdft_launchpad_package`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OperatorAlgebraBridge.cstar_completeCStar_kms_fock_tdft_launchpad_with_bogoliubov_projector_package`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OperatorAlgebraBridge.cstar_completeCStar_kms_fock_tdft_launchpad_with_projectorSuperPair_base_package`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/OperatorAlgebraKKBridge.lean`

- **`InfoGeometry.Canonical.OperatorAlgebraBridge.kk_supercomm_compact_of_even_rep`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.KK.KasparovCycle`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/OperatorAlgebraModularAtom.lean`

- **`InfoGeometry.Canonical.OperatorAlgebraBridge.modular_atom_is_cl11`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/OperatorialInformationLift.lean`

- **`InfoGeometry.Canonical.OperatorialInformationLift.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.OperatorialInformationLift.instCompleteSpaceEndH`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.YangMillsContinuum.EndH`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.OperatorialInformationLift.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OperatorialInformationLift.instIsTopologicalRingEndH`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OperatorialInformationLift.normalized_logTransportedThermalOperatorialInformationLift_of_vacuumTransported`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OperatorialInformationLift.operatorialInformationLift_of_normalized`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OperatorialInformationLift.transportedDiracOperatorialInformationLift_of_strictSymmetry`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OperatorialInformationLift.transportedThermalOperatorialInformationLift_of_strictSymmetry`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/PartitionHierarchy.lean`

- **`InfoGeometry.Canonical.PartitionHierarchy.effectivePotential_eq_neg_inv_temp_mul_log_fiberPartition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PartitionHierarchy.grandCanonical_freeEnergy_eq_trivialEffectivePotential`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.PartitionHierarchy.grandCanonical_potential_eq_trivialLogPartitionPotential`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.PartitionHierarchy.grandCanonical_potentialGC_eq_trivialLogPartitionPotential`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PartitionHierarchy.totalPartition_eq_sum_fiberPartition`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.PartitionHierarchy.boltzmannWeight`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/PerelmanWCore.lean`

- **`InfoGeometry.Canonical.PerelmanW.WFunctional_monotone_of_nonneg_dissipation`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.PerelmanW.WFunctional`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/PerelmanWSpinorial.lean`

- **`InfoGeometry.Canonical.PerelmanW.deriv_W_eq_abs_spinorial_of_normalized_tracking`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.PerelmanW.spinorialWDissipation`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.PerelmanW.spinorialWDissipation_eq_abs_spinorial_of_normalized_tracking`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.RicciMongeAmpere.spectralBasepointLogVolume`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/PolarizedMadelungBridge.lean`

- **`InfoGeometry.Canonical.PolarizedMadelungBridge.PolarizedDoubledAmplitude.kreinExpectation_smul_id_of_mem_minusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PolarizedMadelungBridge.PolarizedDoubledAmplitude.kreinExpectation_smul_id_of_mem_plusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PolarizedMadelungBridge.PolarizedDoubledAmplitude.modularConjugationJ_phaseOrbit_eq_reverse`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PolarizedMadelungBridge.PolarizedDoubledAmplitude.phaseOrbit_eq_dilationOrbit`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PolarizedMadelungBridge.PolarizedDoubledAmplitude.phaseOrbit_zero`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.PolarizedMadelungBridge.PolarizedDoubledAmplitude.ψ`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.PolarizedMadelungBridge.PolarizedDoubledAmplitude.sheet_decomposition`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.PolarizedMadelungBridge.PolarizedDoubledAmplitude.ψ`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.PolarizedMadelungBridge.PolarizedDoubledAmplitude.ψminus_mem_minusSheet`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.PolarizedMadelungBridge.PolarizedDoubledAmplitude.ψ`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.PolarizedMadelungBridge.PolarizedDoubledAmplitude.ψplus_mem_plusSheet`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.PolarizedMadelungBridge.PolarizedDoubledAmplitude.ψ`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.PolarizedMadelungBridge.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.PolarizedMadelungBridge.kreinExpectation_minusPoint`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PolarizedMadelungBridge.kreinExpectation_plusPoint`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PolarizedMadelungBridge.norm_sq_minusPoint`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.SplitQuadraticSheets.minusPoint`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.PolarizedMadelungBridge.norm_sq_plusPoint`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.SplitQuadraticSheets.plusPoint.eq_1`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/PositiveRayCore.lean`

- **`InfoGeometry.Canonical.PositiveRayCore.Z_gaugeSection`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Projective.Normalize.Z_normalizeOnProj`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.PositiveRayCore.exp_logDensity`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.PositiveRayCore.logDensity`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.PositiveRayCore.gaugeSection_eq_exp_logDensity`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.PositiveRayCore.logDensity`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.PositiveRayCore.gaugeSection_eq_exp_neg_modularPotential`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.PositiveRayCore.logDensity`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.PositiveRayCore.gaugeSection_mk`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.PositiveMeasure.normalize`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.PositiveRayCore.logDensity_eq_neg_modularPotential`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PositiveRayCore.modularPotential_eq_neg_logDensity`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PositiveRayCore.ofConeInteriorStateSpace_toConeInteriorStateSpace`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.PositiveRayCore.ofConeInteriorStateSpace`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.PositiveRayCore.toConeInteriorStateSpace_ofConeInteriorStateSpace`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Projective.coneInteriorStateSpaceToProjectiveClass_apply`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/QuantumInference.lean`

- **`InfoGeometry.Canonical.QuantumInference.CCR.comm_a_a`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.QuantumInference.CCR.comm_a_adag`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.QuantumInference.CCR.comm_adag_adag`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RGFlow.lean`

- **`InfoGeometry.Canonical.RGFlow.betaFunction_constantFlow`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RGFlow.constantFlow_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RGFlow.dualDeriv_constantFlow`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RGFlow.dual_map_deriv_eq_zero_at_stationary_scale`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RGFlow.existsUnique_fixedPoint_of_contracting`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RGFlow.exists_isStationaryAtScale_constantFlow`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.RGFlow.IsStationaryAtScale`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RGFlow.generatedDiscreteFlow_succ`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RGFlow.generatedDiscreteFlow_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RGFlow.modularCliffordFlowInvariant_constantFlow_id`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RGFlow.modularCliffordFlowInvariant_id_of_flowInvariant`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.RGFlow.FlowInvariantAtScale`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RGFlow.tendsto_generatedDiscreteFlow_fixedPoint_of_contracting`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RealBdG.lean`

- **`InfoGeometry.Canonical.RealBdG.KConjugate_comp_modularK`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RealBdG.KLinearPart_add_KAntilinearPart`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RealBdG.RealBdGDatum.H_KLinear`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RealBdG.RealBdGDatum.H_chiral`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RealBdG.RealBdGDatum.PH_KAnti`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RealBdG.RealBdGDatum.PH_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RealBdG.RealBdGDatum.TR_KAnti`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RealBdG.RealBdGDatum.TR_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RealBdG.complexI_action_eq_modularK`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RealBdG.modularK_apply_modularK`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RealBdG.modularK_comp_KConjugate`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RealBdG.modularK_def`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RealBdG.modularK_eq_modularComplexI`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RealBdG.modularK_sq`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/RealBdGSheetBridge.lean`

- **`InfoGeometry.Canonical.RealBdGSheetBridge.KAntilinearPart_liftedOperator_eq_zero_of_isGaugeBalanced`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RealBdGSheetBridge.KLinearPart_liftedOperator_eq_liftedOperator_of_isGaugeBalanced`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RealBdGSheetBridge.chiralImbalanceLift_is_KAntilinear`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RealBdGSheetBridge.commonModeLift_is_KLinear`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RealBdGSheetBridge.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RealBdGSheetBridge.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RealBdGSheetBridge.minusBlockMap_dualSheetChiralLift`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RealBdGSheetBridge.minusToPlusBlockMap_dualSheetChiralLift`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RealBdGSheetBridge.plusBlockMap_dualSheetChiralLift`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RealBdGSheetBridge.plusToMinusBlockMap_dualSheetChiralLift`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RelativePotentialCore.lean`

- **`InfoGeometry.Canonical.RelativePotentialCore.gaugeSection_eq_relativeDensity_mul_gaugeSection`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.PositiveMeasure.mass`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCore.relativeDensity_cocycle`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.PositiveRayCore.gaugeSection`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCore.relativeDensity_eq_exp_relativeLogDensity`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.PositiveRayCore.gaugeSection`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCore.relativeDensity_self`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.PositiveMeasure.mass`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity_cocycle`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialCore.representativeRelativeLogDensity_cocycle`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity_eq_logDensity_sub_logDensity`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialCore.representativeRelativeLogDensity_eq_log_sub_log`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity_self`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.PositiveRayCore.logDensity`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCore.relativeModularPotential_cocycle`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialCore.representativeModularPotential_cocycle`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCore.relativeModularPotential_eq_neg_relativeLogDensity`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialCore.representativeModularPotential_eq_neg_representativeRelativeLogDensity`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCore.relativeModularPotential_self`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.PositiveRayCore.logDensity`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCore.representativeMassShift_cocycle`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialCore.representativeMassShift`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCore.representativeMassShift_self`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialCore.representativeMassShift`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCore.representativeMassShift_symm`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialCore.representativeMassShift`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCore.representativeModularPotential_cocycle`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialCore.representativeRelativeLogDensity_cocycle`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCore.representativeModularPotential_scale_left`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.PositiveMeasure.scale`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCore.representativeModularPotential_scale_right`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialCore.representativeRelativeLogDensity_scale_right`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCore.representativeRelativeDensity_eq_exp_representativeRelativeLogDensity`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.PositiveMeasure.mass`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCore.representativeRelativeDensity_scale_left`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.PositiveMeasure.scale_apply`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCore.representativeRelativeDensity_scale_right`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCore.representativeRelativeLogDensity_cocycle`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialCore.representativeRelativeLogDensity_eq_log_sub_log`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCore.representativeRelativeLogDensity_eq_log_sub_log`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.PositiveMeasure.mass`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCore.representativeRelativeLogDensity_scale_scale`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean`

- **`InfoGeometry.Canonical.RelativePotentialCountBridge.averagedKreinTomitaTakesakiOp_apply`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.averagedProjectiveCountHamiltonian_eq_averagedRawCountHamiltonian_sub_massShift`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.averagedProjectiveCountHamiltonian_eq_mean_projectiveCountHamiltonianProfile`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialCountBridge.averagedProjectiveCountHamiltonian`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.averagedProjectiveCountKreinTomitaTakesakiOp_apply`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialCountBridge.averagedProjectiveCountKreinTomitaTakesakiOp`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.averagedRawCountKreinTomitaTakesakiOp_apply`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.averagedRawCountTomitaTakesakiOp_apply`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialCountBridge.averagedRawCountTomitaTakesakiOp`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.countMassShift_cocycle`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialCountBridge.positiveMeasureOfCounts`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.countMassShift_self`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialCountBridge.positiveMeasureOfCounts`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.countMassShift_symm`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialCountBridge.positiveMeasureOfCounts`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.countMass_ne_zero`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialCountBridge.countMass`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.countMass_pos`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialCountBridge.positiveMeasureOfCounts`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.countRelativeVolumeChange_pos`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialCountBridge.countMass`
  - Tags: `statement-bearing`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.exp_neg_countMassShift_eq_countRelativeVolumeChange`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.gaugeSection_countRay_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.meanLogDeltaProfile_mul`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveCountDelta_cocycle`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveCountDelta_eq_exp_neg_projectiveCountModularProfile`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveCountDelta_eq_massRatio_mul_rawCountDelta`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveCountDelta_eq_raw_div_countRelativeVolumeChange`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveCountDelta_self`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveCountHamiltonianProfile_cocycle`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveCountHamiltonianProfile_self`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveCountLogDelta_cocycle`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveCountLogDelta_eq_rawCountLogDelta_add_massShift`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveCountLogDelta_eq_relativeLogDensity_countRay`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveCountLogDelta_self`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveCountModularProfile_eq_raw_sub_scalarModularPotential_relativeVolumeChange`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveLogGenerator_countRay_eq_neg_relativeCountLogDensity_sub_massShift`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.rawCountDelta_cocycle`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.relativeCountDensity_eq_exp_neg_relativeCountModularProfile`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialCountBridge.relativeCountDensity`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.relativeCountLogDensity_cocycle`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.relativeDensity_countRay_eq_massRatio_mul_relativeCountDensity`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialCore.relativeDensity_mk_eq_massRatio_mul_representativeRelativeDensity`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.relativeKreinTomitaTakesakiOp_apply`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialCountBridge.relativeKreinTomitaTakesakiOp`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.relativeLogDensity_countRay_eq_relativeCountLogDensity_add_massShift`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialCountBridge.positiveMeasureOfCounts`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.relativeModularPotential_countRay_eq_neg_relativeCountLogDensity_sub_massShift`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialCore.relativeModularPotential_mk_eq_representativeModularPotential_sub_massShift`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.relativeTomitaTakesakiOp_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.representativeModularPotential_positiveMeasureOfCounts_eq_relativeCountModularProfile`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.representativeRelativeDensity_positiveMeasureOfCounts_eq_relativeCountDensity`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.representativeRelativeLogDensity_positiveMeasureOfCounts_eq_relativeCountLogDensity`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RelativePotentialDiscreteBridge.lean`

- **`InfoGeometry.Canonical.RelativePotentialDiscreteBridge.normalize_toProjectiveState`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.MeasureProjective.Normalized.normalize_pmfToProjectiveState`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/RelativePotentialScalarBridge.lean`

- **`InfoGeometry.Canonical.RelativePotentialScalarBridge.exp_neg_scalarModularPotential_eq`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialScalarBridge.scalarModularPotential_eq_neg_log`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialScalarBridge.scalarLogDensity_eq_log`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialScalarBridge.scalarPositiveMeasure`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialScalarBridge.scalarModularPotential_weylRescale_eq_sub_log`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialScalarBridge.scalarModularPotential_eq_neg_log`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativePotentialScalarBridge.scalarPositiveMeasure_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean`

- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.densityMatrixOfFinProb_diag`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.densityMatrixOfFinProb_offdiag`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.diagonalExpectation_firstQuantize`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.entropy_eq_diagonalExpectation_surprisalOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.firstQuantize_smul`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.hasDerivAt_informationPartitionFunction_zero_relativeTomitaTakesakiOp`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.hasDerivAt_logInformationPartitionFunction_zero_relativeCountLift_of_normalized`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.hasDerivAt_logInformationPartitionFunction_zero_relativeTomitaTakesakiOp_of_normalized`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.instCompleteSpaceEndHRouterAmplitude`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.YangMillsContinuum.EndH`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.instIsTopologicalRingEndHRouterAmplitude`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.logDensityOperator_diag`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.relativeCountModularPotentialOperator_cocycle`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.relativeKreinTomitaTakesakiOp_eq_diagonalAverage_rawLift_smul_eps`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.relativeLogDensityOperator_eq_logDensityOperator_sub`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.relativeModularHamiltonian_sub_countMassShift_cocycle`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.relativeModularPotentialOperator_eq_logDensity_base_sub`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.relativeTomitaTakesakiOp_eq_diagonalAverage_rawLift_smul_id`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.surprisalOperator_diag`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RestrictedSheetContinuous.lean`

- **`InfoGeometry.Canonical.RestrictedSheetContinuous.GaugeBalancedEquiv.isGaugeBalanced`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.GaugeBalancedEquiv.liftedOperator_eq_dualSheetLift`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.RestrictedSheetContinuous.GaugeBalancedEquiv`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.GaugeBalancedEquiv.minusProjectorFlux_liftedOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.GaugeBalancedEquiv.plusProjectorFlux_liftedOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.RestrictedSheetContinuousEquiv.ext_iff`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.RestrictedSheetContinuous.RestrictedSheetContinuousEquiv`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.RestrictedSheetContinuousEquiv.liftedOperator_apply_to_doubled`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.RestrictedSheetContinuousEquiv.minusBlockMap_liftedOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.RestrictedSheetContinuousEquiv.minusProjectorFlux_liftedOperator`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.RestrictedSheetContinuousEquiv.minusToPlusBlockMap_liftedOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.RestrictedSheetContinuousEquiv.minus_inv`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.RestrictedSheetContinuousEquiv.minus_mul`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.RestrictedSheetContinuousEquiv.minus_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.RestrictedSheetContinuousEquiv.plusBlockMap_liftedOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.RestrictedSheetContinuousEquiv.plusProjectorFlux_liftedOperator`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.RestrictedSheetContinuousEquiv.plusToMinusBlockMap_liftedOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.RestrictedSheetContinuousEquiv.plus_inv`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.RestrictedSheetContinuousEquiv.plus_mul`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.RestrictedSheetContinuousEquiv.plus_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.ShaleStinespringEquiv.liftedOperator_coe`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.ShaleStinespringEquiv.liftedOperator_mul`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.RestrictedSheetContinuous.RestrictedSheetContinuousEquiv.liftedOperator_mul`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.ShaleStinespringEquiv.minusProjectorFlux_liftedOperator`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.ShaleStinespringEquiv.plusProjectorFlux_liftedOperator`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.RestrictedSheetContinuous.RestrictedSheetContinuousEquiv.plusProjectorFlux_liftedOperator`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.ShaleStinespringEquiv.val_inv`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.ShaleStinespringEquiv.val_mul`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.ShaleStinespringEquiv.val_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.SheetRestriction.inv_mem`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.SheetRestriction.mul_mem`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.gaugeBalancedSheetRestriction_holds_iff`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RestrictedVolumeCharacter.lean`

- **`InfoGeometry.Canonical.RestrictedVolumeCharacter.RestrictedSheetEquiv.restrictedVolumeCharacter_eq_one_of_weylGaugeBalanced`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedVolumeCharacter.RestrictedSheetEquiv.restrictedVolumeCharacter_inv`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedVolumeCharacter.RestrictedSheetEquiv.restrictedVolumeCharacter_weylGaugeRescaleByScalar`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedVolumeCharacter.RestrictedSheetEquiv.restrictedVolumeScale_weylGaugeRescale`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedVolumeCharacter.RestrictedSheetEquiv.splitWeylCharacter_fst`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedVolumeCharacter.RestrictedSheetEquiv.splitWeylCharacter_snd`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedVolumeCharacter.RestrictedSheetEquiv.volumeScale_trans`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedVolumeCharacter.commonWeylScale_add_relativeSheetScale`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedVolumeCharacter.commonWeylScale_sub_relativeSheetScale`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedVolumeCharacter.dualSheetDiagonalScalarOp_apply_to_doubled`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedVolumeCharacter.dualSheetDiagonalScalarOp_eq_isotropicWeylPart_add_chiralDilationPart`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.MongeAmpereDualSheetBridge.minusPointL`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RestrictedVolumeCharacter.dualSheetDiagonalScalarOp_one_neg_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedVolumeCharacter.dualSheetDiagonalScalarOp_one_one`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RestrictedVolumeCharacter.dualSheetLift_eq_dualSheetPairLift_same`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedVolumeCharacter.dualSheetPairLift_apply_to_doubled`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RestrictedVolumeCharacter.minusBlockMap_dualSheetDiagonalScalarOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedVolumeCharacter.minusProjectorFlux_dualSheetDiagonalScalarOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedVolumeCharacter.minusProjectorFlux_dualSheetPairLift`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RestrictedVolumeCharacter.minusToPlusBlockMap_dualSheetDiagonalScalarOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedVolumeCharacter.plusBlockMap_dualSheetDiagonalScalarOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedVolumeCharacter.plusProjectorFlux_dualSheetDiagonalScalarOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedVolumeCharacter.plusProjectorFlux_dualSheetPairLift`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RestrictedVolumeCharacter.plusToMinusBlockMap_dualSheetDiagonalScalarOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RicciMongeAmpere.lean`

- **`InfoGeometry.Canonical.RicciMongeAmpere.RicciData.symmetric`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.SplitVielbein.minus_norm`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.SplitVielbein.orthogonal`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.StrongRicciFromHessian.nonneg`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.StrongRicciFromHessian.ricci_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.StrongRicciFromHessian.ricci_eq_metric`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.StrongRicciFromHessian.symmetric`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.einsteinEquationAt_of_vacuum`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.einsteinTensor_transport_split_eq_metric_multiple`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.RicciMongeAmpere.RicciTensor`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.einsteinTensor_transport_split_mixed_eq_zero_of_scalar_closure`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry.H`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.isEinsteinKaehlerAtWith_to_exists`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.kaehlerRicciEvolution_beta_eq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.metricLogDet_fderiv_apply_differentiableAt`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.RicciMongeAmpere.MetricLogDetTwiceDifferentiable`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.mongeAmpereConsistentAtBasepoint`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.SpectralInference.InfoSpectralTriple.x₀`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.normalizedKaehlerRicci_beta_eq_neg_spinorial`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.RicciMongeAmpere.normalizedKaehlerRicci_beta_eq_neg`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.normalizedKaehlerRicci_zero_implies_fixedpoint`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.ricci_tensor_invariant_at_fixed_point`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.RicciMongeAmpere.RicciFlow`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.satisfiesKaehlerRicciEvolution_iff`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.satisfiesMongeAmperePotential_iff`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.satisfiesMongeAmperePotential_of_satisfiesMongeAmpere_eq_exp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.satisfiesMongeAmpere_iff`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.scalarCurvatureOnFrame_eq_einstein_multiple`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.scalarModularPotential_mongeAmpereDensity_eq_neg_metricLogDet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.scalarRicci_invariant_at_fixed_point`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.RicciMongeAmpere.ScalarRicciFlow`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.spinorialScalarCurvature_eq_zero_of_normalized_fixedpoint`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.RicciMongeAmpere.spectralBasepointLogVolume`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.vacuumEinsteinAt_implies_on_transportedSplit`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.vacuumEinsteinEquation_of_scalar_relation`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry.H`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.vacuumEinsteinEquation_of_spinorial_scalar`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.RicciMongeAmpere.spinorialScalarCurvature`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.vacuumOnTransportedSplit_iff_curvature_action_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.vacuum_on_transportedSplit_of_curvature_action_zero`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry.H`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/RobustThermodynamicRegression.lean`

- **`InfoGeometry.Canonical.FUSION.phase_transition_catastrophe`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RosettaScaleTransport.lean`

- **`InfoGeometry.Canonical.Rosetta.isJordanKKTGeometry_of_weylScaleTransportShadow`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Rosetta.kk_analyticalIndex_eq_of_weylScaleTransport`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.KK.KasparovCycle`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.Rosetta.weylScaleTransportScalarShadow_eq_jordanBregman_of_isJordanKKTGeometry`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RosettaSourceBridge.lean`

- **`InfoGeometry.Canonical.Rosetta.instCompleteSpaceVCl11DoubledCore`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.RealMajoranaCategory.cl11DoubledCore`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.Rosetta.modularComplexI_toLinearMap_eq_realMajoranaKAxis`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/Singular.lean`

- **`InfoGeometry.Canonical.EinsteinAnomaly_eq_zero_of_regularization_pair`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.EinsteinAnomaly_eq_zero_of_selfAdjoint_idempotent`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.einsteinAnomaly_skew_adjoint`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.EinsteinAnomaly`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.exists_drazinInverse_endomorphism_of_isUnit`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.exists_drazinInverse_of_isUnit`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.exists_drazinInverse_of_idempotent`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.exists_moorePenroseInverse_endomorphism_of_isUnit`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.exists_moorePenroseInverse_of_isUnit`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.exists_moorePenroseInverse_of_selfAdjoint_idempotent`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.exists_regularization_pair_of_isUnit`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.exists_regularization_pair_of_selfAdjoint_idempotent`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/SingularBoundaryCorrection.lean`

- **`InfoGeometry.Canonical.SingularBoundaryCorrection.boundaryGenerator_eq_zero_of_projectors_commute`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.SingularBoundaryCorrection.leftProjector`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.SingularBoundaryCorrection.boundaryGenerator_skew`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SingularBoundaryCorrection.dilationOperator_eq_half_sub_mp_projectors`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.SingularBoundaryCorrection.dilation_eq_half_sub_mp_projectors`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.SingularBoundaryCorrection.dilation_commutator_decomposes_boundaryGenerator`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.InverseKernel.metricProjector`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.SingularBoundaryCorrection.projectors_commute_of_boundaryGenerator_eq_zero`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.SingularBoundaryCorrection.leftProjector`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.SingularBoundaryCorrection.rightBoundaryGenerator_eq_projector_commutator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/SingularTransportSystem.lean`

- **`InfoGeometry.Canonical.SingularTransportSystem.anomalyTerm_eq_projector_commutator_norm`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.SingularTransportSystem.anomalyTerm_eq_boundaryScale`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.SingularTransportSystem.boundaryGenerator_eq_projector_commutator`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.SingularBoundaryCorrection.boundaryGenerator_eq_projector_commutator`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.SingularTransportSystem.boundaryGenerator_eq_zero_iff_projectors_commute`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.SingularBoundaryCorrection.boundaryGenerator_eq_zero_iff_projectors_commute`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.SingularTransportSystem.boundaryScale_eq_projectorObstruction_norm`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.SingularBoundaryCorrection.boundaryScale_eq_projectorObstruction_norm`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.SingularTransportSystem.dilation_commutator_decomposes_boundaryGenerator`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.SingularBoundaryCorrection.dilation_commutator_decomposes_boundaryGenerator`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.SingularTransportSystem.logarithmicDivergence_split`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.SingularTransportSystem.logDivergence_split`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.SingularTransportSystem.regular_radial_transport_closes_of_boundaryScale_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/SinkhornFoundation.lean`

- **`InfoGeometry.Canonical.MoE.SinkhornCertificate.leftScale_pos`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.SinkhornCertificate.rightScale_pos`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.bayesianFreeEnergyObjective_eq_regularizedOTObjective`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.colLyapunov_colNormalize_eq_zero`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.MoE.colSum`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.colLyapunov_nonneg`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.colNormalize_has_unit_colMarginal`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.MoE.Coupling`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.colRNBarrier_colNormalize_eq_zero`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.MoE.colSum`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.colRNBarrier_nonneg`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.entropicOptimalTransportObjective_eq_transport_plus_entropy`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.exists_perm_decomposition_of_bistochastic`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.MoE.switchMatrix`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.exists_perm_decomposition_of_sinkhornBalanced`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.MoE.switchMatrix`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.gc_gibbsWeight_eq_normalizedWeights`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.gc_partition_eq_routerPartition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.kahlerPotentialRN_eq_scalarModularPotential_relativeVolumeChangeRN`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialScalarBridge.scalarModularPotential_eq_neg_log`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.normalizedWeights_nonneg`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.MoE.routerPartition`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.relativeVolumeChangeRN_eq_exp_logJacobian`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.MoE.colRadonNikodymGenerator`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.rn_barrier_row_step_eq_zero`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.MoE.rowRNBarrier_rowNormalize_eq_zero`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.rowLyapunov_nonneg`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.rowLyapunov_rowNormalize_eq_zero`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.MoE.rowNormalize`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.rowNormalize_has_unit_rowMarginal`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.MoE.Coupling`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.rowRNBarrier_nonneg`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.rowRNBarrier_rowNormalize_eq_zero`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.MoE.rowNormalize`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.schroedingerBridgeStep_monotone`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.MoE.sinkhornStep_regularizedObjective_monotone`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.schroedingerBridgeStep_radonNikodymBarrier_monotone`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.MoE.sinkhornStep_radonNikodymBarrier_monotone`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.sinkhornScaledCoupling_def`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.sinkhornStep_bayesianFreeEnergy_monotone`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.MoE.sinkhornStep_regularizedObjective_monotone`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.sinkhornStep_entropicOT_monotone`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.MoE.sinkhornStep_regularizedObjective_monotone`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.sinkhornStep_radonNikodymBarrier_monotone`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.MoE.sinkhornStep_phaseRNBarrier_monotone`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.sinkhornStep_regularizedObjective_monotone`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.MoE.sinkhornStep_phaseLyapunov_monotone`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.sinkhornTwoStep_eq_bayesianPosteriorGauge`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.MoE.rowNormalize`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.sinkhornTwoStep_eq_schroedingerBridgeGauge`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.MoE.rowNormalize`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.sinkhornTwoStep_eq_twoSidedGauge`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.MoE.rowNormalize`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.switchMatrix_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.switchMatrix_mem_rowStochastic`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.switchMatrix_row_sum_one`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.MoE.normalizedWeights_sum_one`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MoE.trajectoryLyapunovNext_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/SinkhornKMSCore.lean`

- **`InfoGeometry.Canonical.KMSSinkhornBridge.kreinRouterModularHamiltonian_isKreinSelfAdjoint`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KMSSinkhornBridge.routerModularHamiltonian_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KMSSinkhornBridge.sinkhorn_stepwise_kms_bound`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.MoE.trajectoryRNBarrierNext`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/SpectralInference.lean`

- **`InfoGeometry.Canonical.SpectralInference.CertifiedChiralSpectralTriple.exists_of_spectralTriple`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SpectralInference.CertifiedChiralSpectralTriple.metricProjector_idempotent`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.SpectralInference.CertifiedChiralSpectralTriple`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.SpectralInference.CertifiedChiralSpectralTriple.metricProjector_star`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.SpectralInference.CertifiedChiralSpectralTriple`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.SpectralInference.CertifiedChiralSpectralTriple.spectralProjector_idempotent`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.SpectralInference.CertifiedChiralSpectralTriple`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.SpectralInference.CertifiedRegularizedSpectralTriple.exists_of_spectralTriple`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.SpectralInference.CertifiedRegularizedSpectralTriple.toSpectralTriple`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.SpectralInference.CertifiedRegularizedSpectralTriple.spectralProjector_idempotent`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SpectralInference.InfoSpectralTriple.dirac_eq_canonicalDiracOfMetric_of_isPositive`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SpectralInference.InfoSpectralTriple.inner_dirac_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SpectralInference.SpectralTriple.is_self_adjoint`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SpectralInference.bayesianAction_nonneg`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Convex.HessianGeometry.divergence`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.SpectralInference.bayesianAction_succ`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SpectralInference.bayesianAction_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/SpinConnection.lean`

- **`InfoGeometry.Canonical.SpinConnection.U_add`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SpinConnection.U_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.transportEnd_add`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.transportEnd_lie`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.transportEnd_mul`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/SplitCliffordThermalBridge.lean`

- **`InfoGeometry.Canonical.SplitCliffordThermalBridge.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.SplitCliffordThermalBridge.splitCliffordThermalBridge_of_strictSymmetry`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SplitCliffordThermalBridge.transportedThermalFlow_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SplitCliffordThermalBridge.transportedThermalGenerator_eq_transportDirac_of_zeroChemicalPotential`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.BogoliubovFockSuper.HyperbolicMixingParams`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/SuperAnomaly.lean`

- **`InfoGeometry.Canonical.SuperAnomaly.SuperWeightLike.graded_weight_anticommutator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperAnomaly.SuperWeightLike.graded_weight_commutator`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.SuperAnomaly.SuperWeightLike`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.SuperAnomaly.superComm_even_left`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/SuperInference.lean`

- **`InfoGeometry.Canonical.SuperInference.superCharge_boson_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperInference.superCharge_fermion_eq_dualMap`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperInference.susyHamiltonian_eq_self`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/SuperUnified.lean`

- **`InfoGeometry.SuperUnified.SuperKaehlerStructure.J_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.SuperUnified.bracket_boson_boson_is_bosonic`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.SuperUnified.bracket_boson_fermion_is_fermionic`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.SuperUnified.bracket_fermion_fermion_is_bosonic`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.SuperUnified.clifford_decomposition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.SuperUnified.hamiltonian_is_bosonic`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.SuperUnified.symplectic_is_complex_structure`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.SuperUnified.symplecticFormOp`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/TomitaTakesaki.lean`

- **`InfoGeometry.Canonical.TomitaTakesaki.cptAtoms_generate_splitCliffordAlg`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.TomitaTakesaki.iota_range_subset_adjoin_cptAtomSet`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.cptJ_cptJeps_anticommute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.cptJ_sq`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Clifford.splitQ11_apply`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.cptJeps_sq`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Clifford.splitQ11_apply`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.iota_range_subset_adjoin_cptAtomSet`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.TomitaTakesaki.cptAtomSet`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.modularCPTSupercharge_Q_eq_dilationOperator`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.modularCPTSupercharge_hamiltonian`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.modularCPTSupercharge_maps_minus_to_plus`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.inGradeMinus`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.modularCPTSupercharge_maps_plus_to_minus`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.TomitaTakesaki.modularCPTSupercharge`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.modularCPT_supergraded_lie_package`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_sq`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.complex_i_sq`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ_anticommutator_modularSignEpsilon`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ_anticommutes_modularComplexI`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ_anticommutes_modularSign`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.modular_j_spectral_epsilon_anticommute`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ_commutator_modularSignEpsilon`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ_fixed_of_diagonalPositiveTimeVector`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ_fixed_of_positiveTimeVector`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ_fixed_of_diagonalPositiveTimeVector`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ_sq`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.modular_j_involution`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.modularSignEpsilon_isOdd`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.isOdd`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.modularSignEpsilon_sq`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.spectral_epsilon_involution`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.reflectionQuadratic_nonneg_of_diagonalPositiveTimeVector`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.reflectionQuadratic_nonneg_of_positiveTimeVector`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.TomitaTakesaki.PositiveTimeVector`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.tomitaRepresentation_cptEps`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.TomitaTakesaki.modularAtomRepresentation_cptEps`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.tomitaRepresentation_cptJ`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.tomitaRepresentation_cptJeps`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/TopologicalEuler.lean`

- **`InfoGeometry.Canonical.TopologicalEuler.euler_is_invariant`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/TopologicalInvariants.lean`

- **`InfoGeometry.Canonical.TopologicalInvariants.cs_invariant_of_flat`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.TopologicalInvariants.BayesianLoop`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/Triality.lean`

- **`InfoGeometry.Canonical.Triality.GeometricAttentionMap.attention_decomposition_residual`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.Triality.TriadicCore.route`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.Triality.GeometricAttentionMap.attention_def`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Triality.MultiHeadGeometricAttention.preOutput_def`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Triality.splitMetricTriadicInstance_interact`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Triality.splitMetricTriadicInstance_quadK`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Triality.splitMetricTriadicInstance_quadQ`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Triality.splitMetricTriadicInstance_quadV`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Triality.splitMetricTriadicInstance_route`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Triality.splitMetricTriadicInstance_route_norm_compat`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.Triality.MetricTriadicCore.route_norm_compat`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/Unification.lean`

- **`InfoGeometry.Canonical.Unification.AnomalyRosettaStone.h_geo_thermo`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Unification.AnomalyRosettaStone.h_thermo_alg`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Unification.Cl11LatticeRosettaStone.continuous_eq_lattice_shadow`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.Unification.Cl11LatticeRosettaStone.h_transport`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.Unification.instCompleteSpaceContinuousLinearMapRealIdContinuousCarrier`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.ModularAnomaly.Cl11LatticeBridge.ContinuousCarrier`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.Unification.instCompleteSpaceVCl11DoubledCoreFinModel`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Quantum.RealMajoranaCategory.cl11DoubledCore`
  - Tags: `statement-bearing`, `wrapper-candidate`
- **`InfoGeometry.Canonical.Unification.instIsTopologicalRingContinuousLinearMapRealIdContinuousCarrier`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Unification.scalarToFockLift_add_const_eq_centralGaugeShift`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/VolumeDeformationPrinciple.lean`

- **`InfoGeometry.Canonical.VolumeDeformationPrinciple.DefectiveVolumeBridge.potential_mul`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.DefectiveMultiplicativeToAdditiveBridge.additiveInvariant_mul`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.VolumeDeformationPrinciple.ExactVolumeBridge.potential_mul`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ExactMultiplicativeToAdditiveBridge.additiveInvariant_mul`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.VolumeDeformationPrinciple.ExactVolumeBridge.potential_mulCommutator_eq_zero`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.AdditiveLinearization.linearize`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/WeylAnomalySource.lean`

- **`InfoGeometry.Canonical.WeylInformationGauge.nonzeroAnomaly_sources_transportedEinsteinResidual`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ConformalUnification.ConformalInference`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/WeylGaugeField.lean`

- **`InfoGeometry.Canonical.WeylDifferentialOperator.map_add_apply`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.WeylDifferentialOperator`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.WeylDifferentialOperator.map_neg`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.WeylDifferentialOperator.map_smul`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.WeylDifferentialOperator.map_smul_apply`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.WeylDifferentialOperator.map_smul`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.WeylDifferentialOperator.map_zero`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.WeylDifferentialOperator.map_smul`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.WeylDifferentialOperator.nilpotent_apply`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.WeylDifferentialOperator.nilpotent`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.WeylGaugeField.along_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeField.respond_transformByPotential_eq_of_isGaugeInvariant`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeField.respond_transform_eq_of_isGaugeInvariant`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeField.transformSection_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeField.transform_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeField.transform_comp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeField.transform_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/WeylGaugeOperatorLift.lean`

- **`InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.determinantCharacter_eq_one_of_isGaugeBalanced`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.isotropicGaugeTransport_commutes_relativeDilationTransport`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.liftedOperator_mulTransport`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.liftedOperator_referenceTransport`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.MongeAmpereDualSheetBridge.minusPointL`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.liftedOperator_referenceTransport_eq_gauge_smul_epsilonBoost`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.logRelativeVolumePotential_eq_logPlus_minus_logMinus`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Volume.DeterminantBundle.volumeScale`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.logRelativeVolumePotential_eq_two_mul_relativeLogCoordinate`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.logMinusVolume`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.logRelativeVolumePotential_mulTransport`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.minusBlockMap_liftedOperator`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.liftedOperator`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.minusProjectorFlux_liftedOperator`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.liftedOperator`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.minusToPlusBlockMap_liftedOperator`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.MongeAmpereDualSheetBridge.minusToPlusBlockMap`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.plusBlockMap_liftedOperator`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.liftedOperator`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.plusProjectorFlux_liftedOperator`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.RestrictedVolumeCharacter.plusProjectorFlux_dualSheetPairLift`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.plusToMinusBlockMap_liftedOperator`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.liftedOperator`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.relativeVolumeScale_eq_abs_character`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.toRestrictedSheetEquiv`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.relativeVolumeScale_gaugeRescale`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.relativeVolumeScale_pos`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Volume.DeterminantBundle.volumeScale`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/WeylPathHysteresis.lean`

- **`InfoGeometry.Canonical.WeylInformationGauge.twistedInference_updateOrderPathDependent`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.WeylInformationGauge.UpdateOrderPathDependent`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.WeylInformationGauge.weylOrderWitnessMatrix2_positiveCols_afterRow`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.WeylInformationGauge.weylOrderWitnessMatrix2`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.WeylInformationGauge.weylOrderWitnessMatrix2_positiveRows_afterCol`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.WeylInformationGauge.weylOrderWitnessMatrix2`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/WeylTransport.lean`

- **`InfoGeometry.Canonical.ScaleEquivariantFlow.transportObservable_isCocycle`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeField.connectionAlong_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeField.covariantGeneratedFlow_scaleOf_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeField.covariantSectionAlong_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeField.covariantSectionAlong_transform_eq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeField.curvatureAlong_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeField.generatedAlong_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeField.respondCovariantFlow_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeField.respondCovariantFlow_transform_eq`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.WeylGaugeField.transformByPotential`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.WeylGaugeField.responseAlong_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeField.responseAlong_eq_along_comp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylLineIntegrator.gaugeCompensatedHolonomy_eq_base_of_boundary_law`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylLineIntegrator.integrateCurvature_transformByPotential_eq`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.WeylLineIntegrator`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/WeylTransportChiralBridge.lean`

- **`InfoGeometry.Canonical.WeylTransportBridge.finiteSum_holonomy_eq_chiralScale_of_flat`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.ConformalUnification.ConformalInference`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.WeylTransportBridge.holonomy_eq_zero_of_flat_of_unitRelativeVolume`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/YangMillsContinuum.lean`

- **`InfoGeometry.Canonical.YangMillsContinuum.IBSampledFlow.sinkhornClosure_of_sampledIB`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.YangMillsContinuum.IBSampledFlow.sinkhornClosure_of_sampledIB_components`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.YangMillsContinuum.IBSampledFlow.sinkhornControl_of_sampledIB_components`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.KMSSinkhornBridge.CommutatorOrthogonalOnOmega`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.TypeIIIModularInterface.infinitesimal_generator_at_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.TypeIIIModularInterface.modularAutomorphismGroup_additive`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.TypeIIIModularInterface.modularHamiltonian_eq_neg_log_rn`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.TypeIIIModularInterface.modularOperator_eq_rn`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.connesRovelliThermalTimeIdentity`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.YangMillsContinuum.EndH`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.deriv_modularAutomorphismGroup_zero_eq_commutator`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.hasDerivAt_modularAutomorphismGroup_zero_eq_commutator`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.deriv_modularShift_zero_eq_commutator`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.YangMillsContinuum.EndH`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.hasDerivAt_modularAutomorphismGroup_zero_eq_commutator`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.instCompleteSpaceEndH`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.YangMillsContinuum.EndH`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.modularAutomorphismGroup_add`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.modular_shift`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.modularAutomorphismGroup_additive`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.YangMillsContinuum.EndH`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.modularAutomorphismGroup_zero`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.modularHamiltonian_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.modularOperator_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.toAdditiveModularFlow_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/YangMillsFiniteBridge.lean`

- **`InfoGeometry.Canonical.YangMillsFinite.FiniteYangMillsBridge.existenceClaims_of_bridge`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.YangMillsFinite.FiniteYangMillsBridge.gamma_le_spectral_gap`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.YangMillsFinite.FiniteYangMillsBridge.obligations_of_expectationSeedFromLogDet`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.GaugeGroups.SUN`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.YangMillsFinite.spectralGapFromLogDet_pos_of_coercive`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.KMSSinkhornBridge.jacobianRelativeVolume`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/YangMillsFiniteQFT.lean`

- **`InfoGeometry.Canonical.YangMillsFinite.FiniteQFTLayer.expectationSeedReflectionPositivity_of_jointKernel_commutator`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.KMSSinkhornBridge.CommutatorOrthogonalOnOmega`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/ZetaDeterminant.lean`

- **`InfoGeometry.Canonical.Determinant.SpectralZetaLogDetData.cutoff_ne_zero'`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.Determinant.SpectralZetaLogDetData`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.Determinant.SpectralZetaLogDetData.logDet_eq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Determinant.capstone_logAbsVolume_add_from_zeta`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.Determinant.zetaRegularizedLogVolume_add`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.Determinant.spectralZetaLogDetDataOfChiralTriple_logDet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Determinant.spectralZetaLogDetDataOfRegularizedTriple_logDet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Determinant.zetaRegularizedLogDet_eq_logAbsDet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Determinant.zetaRegularizedLogDet_mul`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.Determinant.zetaRegularizedDet`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.Determinant.zetaRegularizedLogVolume_add`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Volume.Base.VolumeHom`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.Determinant.zetaRegularizedLogVolume_eq_logAbsVolume`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Core/Entropy.lean`

- **`InfoGeometry.Core.entropy_def`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.expectation_one`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.expectation_const`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.expectation_zero`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.expectation_const`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.klDiv_def`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.logDensity_def`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.surprisal_def`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Core/GrandCanonical.lean`

- **`InfoGeometry.Core.gc2_gibbsWeight_sum_one`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.GrandCanonical.gibbsWeightGC_sum_one`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.gc2_partition_pos`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.GrandCanonicalTwoParam`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.gc2_potential_deriv_beta_eq_neg_meanShift`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.GrandCanonicalTwoParam`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.gc2_potential_deriv_mu_eq_beta_meanNumber`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.GrandCanonicalTwoParam`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.gc_gibbsWeight_sum_one`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.GrandCanonical.gibbsWeight_sum_one`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.gc_hessian_eq_variance`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.gc_potential_second_derivative_eq_variance`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.gc_hessian_nonneg`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.GrandCanonical.hessian_nonneg`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.gc_partition_pos`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.GrandCanonical.partition_pos`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.gc_potential_deriv_eq_neg_mean`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.GrandCanonical.potential_deriv_eq_neg_mean`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.gc_potential_second_derivative_eq_variance`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.GrandCanonical.potential_second_derivative_eq_variance`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Core.gc_spinodal_iff_variance_eq_zero`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.GrandCanonical.spinodal_iff_variance_eq_zero`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Core/Involution.lean`

- **`InfoGeometry.Core.InvolutiveAutomorphism.ext_iff`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.InvolutiveAutomorphism.ext`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.InvolutiveAutomorphism.map_add`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.PreservesLinear`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.InvolutiveAutomorphism.map_lie`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Core.PreservesLieBracket`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Core.InvolutiveAutomorphism.map_mul`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Core.PreservesMul`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Core.InvolutiveAutomorphism.map_neg`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Core.PreservesLinear`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Core.InvolutiveAutomorphism.map_one`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Core.PreservesMul`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Core.InvolutiveAutomorphism.map_smul`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.PreservesLinear`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.LinearInvolutiveAutomorphism.involutive`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.PreservesLinear`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.LinearInvolutiveAutomorphism.map_add`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.LinearInvolutiveAutomorphism.map_neg`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.LinearInvolutiveAutomorphism.map_smul`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.LinearInvolutiveAutomorphism.map_sub`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.MulInvolutiveAutomorphism.involutive`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.PreservesMul`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.MulInvolutiveAutomorphism.map_div`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.MulInvolutiveAutomorphism.map_inv`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.MulInvolutiveAutomorphism.map_mul`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.MulInvolutiveAutomorphism.map_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.Projector.fixed_iff_minus_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.Projector.minus_add`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.PreservesLinear`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.Projector.minus_idempotent`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.PreservesLinear`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.Projector.minus_plus`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.PreservesLinear`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.Projector.minus_smul`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.PreservesLinear`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.Projector.neg_fixed_iff_plus_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.Projector.plus_add`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.PreservesLinear`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.Projector.plus_idempotent`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.PreservesLinear`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.Projector.plus_minus`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.PreservesLinear`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.Projector.plus_smul`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.PreservesLinear`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.cartanMinus_neg_fixed`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Core.PreservesLinear`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Core.cartanPlus_fixed`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Core.PreservesLinear`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Core.cartan_decomposition`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Core.PreservesLinear`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Core.instPreservesLieBracketOfPreservesLie`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.PreservesLie.toPreservesLieBracket`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.instPreservesLinearOfPreservesLie`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.PreservesLie.toPreservesLinear`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Core/Jordan.lean`

- **`InfoGeometry.Core.SPD_posDef`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.spd_pos_def`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.SPD_transpose_eq_self`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.spd_transpose_eq_self`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.spd_pos_def`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Jordan.SPD.posDef`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Core.spd_transpose_eq_self`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Jordan.SPD.transpose_eq_self`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Core/SymmetricLie.lean`

- **`InfoGeometry.Core.SymmetricLieAlgebra.bracket_k_k`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.SymmetricLieAlgebra.bracket_k_p`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.SymmetricLieAlgebra.bracket_p_p`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.SymmetricLieAlgebra.cartanForm_orthogonal`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.SymmetricLieAlgebra.convex_minusPart_image`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.SymmetricLieAlgebra.convex_minusPart_preimage`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.SymmetricLieAlgebra.convex_plusPart_image`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.SymmetricLieAlgebra.convex_plusPart_preimage`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.SymmetricLieAlgebra.triple_closed`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.SymmetricLieAlgebra.evenLieSubalgebra`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Core/SymmetricLieGeneric.lean`

- **`InfoGeometry.Core.Generic.SymmetricLieAlgebra.CartanLieAlgebra.killing_nondegenerate`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.Generic.SymmetricLieAlgebra.CartanSignature.neg_on_k`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.Generic.SymmetricLieAlgebra.CartanSignature.pos_on_p`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.Generic.SymmetricLieAlgebra.P_minus_comp_P_plus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.Generic.SymmetricLieAlgebra.P_minus_idempotent`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.Generic.SymmetricLieAlgebra.P_plus_comp_P_minus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.Generic.SymmetricLieAlgebra.P_plus_idempotent`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.Generic.SymmetricLieAlgebra.bracket_k_k`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.Generic.SymmetricLieAlgebra`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.Generic.SymmetricLieAlgebra.bracket_k_p`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.Generic.SymmetricLieAlgebra.bracket_p_p`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.Generic.SymmetricLieAlgebra.cartan_decomposition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.Generic.SymmetricLieAlgebra.involution_apply`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Core.Generic.SymmetricLieAlgebra`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Core.Generic.SymmetricLieAlgebra.killing_orthogonal`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Core/SymmetricSpaces.lean`

- **`InfoGeometry.Core.cartanSymmetry_fixpoint_ofInvolutiveMulAut`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Architecture.cartanSymmetryOfInvolutiveMulAut_fixpoint`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.cartanSymmetry_involutive_ofInvolutiveMulAut`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.InvolutiveMulAut`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.symmetricPairOfInvolutiveMulAut_K_eq_fixed`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Core.symmetricPairOfInvolutiveMulAut`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Core.symmetricPairOfInvolutiveMulAut_K_eq_fixedSubgroup`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.InvolutiveMulAut`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.symmetricPair_K_eq_fixedSubgroup`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Architecture.SymmetricPair.K_eq_fixedSubgroup`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Core/UnifiedGeometry.lean`

- **`InfoGeometry.Core.CartanDecomposition.ext_iff`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.CartanDecomposition.θ`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.CartanLieStructure.bracket_compat`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.SymmetricSpace.ext`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Core.InvolutiveAutomorphism.ext`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Core.SymmetricSpace.ext_iff`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.SymmetricSpace`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.SymmetricSpace.ofLegacy_toLegacy`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.SymmetricSpace.toLegacy_ofLegacy`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.cartanMinus_odd`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.CartanDecomposition.θ`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.cartanOfMulInvolutive_toMulInvolutive`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.InvolutiveAutomorphism.ext`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.cartanPlus_even`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.cartanPlus_fixed`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.cartan_split`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.CartanDecomposition.θ`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.conjugation_bracket_even_even_mem_even`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Core.conjugationMap_bracket`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Core.conjugation_bracket_even_odd_mem_odd`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.conjugationMap_bracket`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.conjugation_bracket_odd_odd_mem_even`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.conjugationMap_bracket`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.mulInvolutiveOfCartan_toCartan`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Core.reflection_involutive`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.SymmetricSpace`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Core.reflection_self`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Core.SymmetricSpace.reflection_fix`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/GrandCanonical/Core.lean`

- **`InfoGeometry.GrandCanonical.deriv_partition`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.GrandCanonical.GrandCanonicalParams`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.GrandCanonical.deriv_partitionDerivFun`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.GrandCanonical.hasDerivAt_partitionDerivFun`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.GrandCanonical.gibbsWeightGC_nonneg`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.GrandCanonical.gibbsWeightGC`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.GrandCanonical.gibbsWeightGC_pos`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.GrandCanonical.gibbsWeightGC`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.GrandCanonical.gibbsWeightGC_sum_one`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.GrandCanonical.gibbsWeightGC`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.GrandCanonical.gibbsWeight_nonneg`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.GrandCanonical.GrandCanonicalParams`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.GrandCanonical.gibbsWeight_pos`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.GrandCanonical.GrandCanonicalParams`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.GrandCanonical.gibbsWeight_sum_one`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.GrandCanonical.GrandCanonicalParams`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.GrandCanonical.hasDerivAt_partition`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.GrandCanonical.GrandCanonicalParams`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.GrandCanonical.hasDerivAt_partitionDerivFun`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.GrandCanonical.hasDerivAt_partitionDerivTerm`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.GrandCanonical.hasDerivAt_partitionDerivTerm`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.GrandCanonical.GrandCanonicalParams`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.GrandCanonical.hasDerivAt_partitionGC_beta`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.GrandCanonical.shiftedEnergy`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.GrandCanonical.hasDerivAt_partitionGC_mu`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.GrandCanonical.partitionGCDerivMuFun`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.GrandCanonical.meanNumber_eq_firstNumber_div_partition`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.GrandCanonical.firstNumberUnnormalized`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.GrandCanonical.meanShift_eq_firstShift_div_partition`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.GrandCanonical.gibbsWeightGC`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.GrandCanonical.mean_eq_firstMoment_div_partition`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.GrandCanonical.firstMomentUnnormalized`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.GrandCanonical.secondMoment_eq_secondMomentUnnormalized_div_partition`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.GrandCanonical.GrandCanonicalParams`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.GrandCanonical.spinodal_iff_energy_eq_mean`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.GrandCanonical.spinodal_iff_variance_eq_zero`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.GrandCanonical.potential_second_derivative_eq_variance`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.GrandCanonical.variance_eq_secondMoment_sub_mean_sq`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.GrandCanonical.gibbsWeight_sum_one`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.GrandCanonical.variance_nonneg`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.GrandCanonical.GrandCanonicalParams`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Jordan/Core.lean`

- **`InfoGeometry.Jordan.jordanProd_add_left`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Jordan.JordanAlgebra.add_left`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Jordan.jordanProd_add_right`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Jordan.jordanProd_comm`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Jordan.JordanAlgebra.comm`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Jordan.jordanProd_identity`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Jordan.JordanAlgebra`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Jordan.jordanProd_smul_left`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Jordan.JordanAlgebra`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Jordan.jordanProd_smul_right`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Jordan.jordanProd_zero_right`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/KK/CompactOperatorBridge.lean`

- **`InfoGeometry.KK.isCompactEnd_of_finiteDimensional`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.KK.isCompactEnd_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Krein/HilbertBridge.lean`

- **`InfoGeometry.Krein.HilbertDoubled.coe_toLp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.HilbertDoubled.ext_iff`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.HilbertDoubled`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Krein.HilbertDoubled.fst_ofWithLp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.HilbertDoubled.fst_toLp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.HilbertDoubled.instCompleteSpace`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.HilbertDoubled`
  - Tags: `statement-bearing`, `wrapper-candidate`
- **`InfoGeometry.Krein.HilbertDoubled.ofLp_toLp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.HilbertDoubled.ofWithLp_val`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.HilbertDoubled.snd_ofWithLp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.HilbertDoubled.snd_toLp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.HilbertDoubled.toLp_ofLp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.HilbertDoubled.val_ofWithLp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.HilbertDoubled.val_toLp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.NeutralSpace.ext_iff`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.NeutralSpace.ext`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Krein.NeutralSpace.fst_coe`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.NeutralSpace.fst_ofWithLp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.NeutralSpace.fst_toLp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.NeutralSpace.fst_val`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.NeutralSpace.instCompleteSpace`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.NeutralSpace`
  - Tags: `high-fan-in`, `statement-bearing`, `wrapper-candidate`
- **`InfoGeometry.Krein.NeutralSpace.neutralLift_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.NeutralSpace.ofWithLp_val`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.NeutralSpace.rotation45_symm_toLp_pair`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.NeutralSpace.snd_coe`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.NeutralSpace.snd_ofWithLp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.NeutralSpace.snd_toLp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.NeutralSpace.snd_val`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.NeutralSpace.val_ofWithLp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.NeutralSpace.val_toLp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/MaxEnt/Core.lean`

- **`InfoGeometry.MaxEnt.ACProbMeasure.ac`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.MaxEnt.ACProbMeasure.coe_eq_of_measure_eq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.MaxEnt.ACProbMeasure.instIsProbabilityMeasureμ`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.MaxEnt.ACProbMeasure`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.MaxEnt.ConstraintsIntegrableOn_of_memFeasibleIntegrable`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.MaxEnt.ACProbMeasure`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.MaxEnt.FeasibleIntegrable_subset_Feasible`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.MaxEnt.ACProbMeasure`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.MaxEnt.IsMaxEntSolution.hasExponentialRNForm_of_finiteSupportDuality`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.MaxEnt.IsMaxEntSolution.toIntegrable`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.MaxEnt.ACProbMeasure`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.MaxEnt.LinearConstraint.measurable_f`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/MaxEnt/DualBridge.lean`

- **`InfoGeometry.MaxEnt.crossEntropyToGibbs_eq_dualObjective`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.MaxEnt.crossEntropyToGibbs_eq`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.MaxEnt.entropy_gibbs_eq_dualObjective`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.MaxEnt.entropy`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.MaxEnt.gibbs_attains_dualObjective`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.MaxEnt.entropy_gibbs_eq_dualObjective`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.MaxEnt.gibbs_form_candidate_maximizes_entropy`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.MaxEnt.MaxEntConstraint`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.MaxEnt.gibbs_maximizes_entropy_on_constraint`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.MaxEnt.gibbs_mem_maxEntConstraint_iff`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.MaxEnt.momentResidual_eq_zero_iff`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Projective/Bridge.lean`

- **`InfoGeometry.Projective.interiorToPositiveMeasure_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Projective.interior_positiveOrthantCone_eq`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Projective.positiveOrthantCone`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Projective.mem_interior_positiveOrthantCone_iff`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Projective.positiveOrthantCone`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Projective.projectiveClassToConeInteriorStateSpace_mk`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Projective.projectiveClassToConeInteriorStateSpace_surjective`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Projective.ConeInteriorStateSpace`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Quantum/AnticommutingInvolutionCore.lean`

- **`InfoGeometry.Quantum.AnticommutingInvolutionCore.eps_comp_J`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Quantum.AnticommutingInvolutionCore.toInvolutionCore`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Quantum.AnticommutingInvolutionCore.j_comp_k`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Quantum.AnticommutingInvolutionCore.toInvolutionCore`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Quantum.AnticommutingInvolutionCore.k_comp_eps`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Quantum.AnticommutingInvolutionCore.toInvolutionCore`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Quantum/AttentionBridge.lean`

- **`InfoGeometry.Quantum.AttentionBridge.attention_source_transports_to_modular`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.AttentionBridge.split_attention_as_residual`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.Triality.TriadicCore.route`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.AttentionBridge.split_softmax_weight_formula`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/BulkBoundary.lean`

- **`InfoGeometry.Quantum.BulkBoundary.PolarizationOdd.maps_minus_to_plus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.BulkBoundary.PolarizationOdd.maps_plus_to_minus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.BulkBoundary.boundaryLocalizedZeroModePair_of_negativePhase_under_bogoliubov_of_simplifiedBoundaryModel_of_preservesPolarization`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.BulkBoundary.bulk_boundary_correspondence_concrete_of_simplifiedBoundaryModel`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.BulkBoundary.bulk_boundary_correspondence_concrete_of_simplifiedBoundaryModel_under_bogoliubov`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.BulkBoundary.exists_zeroMode_of_dim_mismatch`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.BulkBoundary.globalChainOperatorFromOpenChain_cons`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.BulkBoundary.globalChainOperatorFromOpenChain_nil`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.BulkBoundary.zero_mode_is_information_sink`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.BulkBoundary.zero_mode_is_information_sink_concrete_of_simplifiedBoundaryModel`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.BulkBoundary.zero_mode_is_information_sink_concrete_of_simplifiedBoundaryModel_under_bogoliubov`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/BulkBoundaryIndexBridge.lean`

- **`InfoGeometry.Quantum.BulkBoundary.auto_bulk_boundary_correspondence_concrete_from_seed_4`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/CliffordDictionary.lean`

- **`InfoGeometry.Quantum.Cl11Dictionary.J_inv`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.Cl11Dictionary.K_def`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.Cl11Dictionary.K_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.Cl11Dictionary.anticomm`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.Cl11Dictionary.ε_inv`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/CommutingInvolutionCore.lean`

- **`InfoGeometry.Quantum.CommutingInvolutionCore.commuting_involution_four_corners`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.CommutingInvolutionCore.je_comm`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.CommutingInvolutionCore.J_eps_comm`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.CommutingInvolutionCore.je_comm_apply`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Quantum.CommutingInvolutionCore.instModuleCarrier`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Quantum.CommutingInvolutionCore.je_comp_eps`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Quantum.CommutingInvolutionCore.instModuleCarrier`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Quantum.CommutingInvolutionCore.je_def`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.CommutingInvolutionCore.je_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/Fierz.lean`

- **`InfoGeometry.Quantum.Fierz.information_fierz_majorana`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.Fierz.information_fierz_identity`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Quantum/Fock.lean`

- **`InfoGeometry.Quantum.annihilation_kills_vacuum_vector`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.bayesianAddData_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.bayesian_update_preserves_data_independence`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.commutator_I_J`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.commutator_J_epsilon_eq_two_I`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.creation_annihilation_orthogonal`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.data_model_decomposition`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.vacuum_is_zero_ray`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/GeometricTensor.lean`

- **`InfoGeometry.Quantum.GeometricQuantumTensor.berry_alt`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.compat`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.metric_symm`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/Hurwitz.lean`

- **`InfoGeometry.Quantum.Hurwitz.K_sq`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.RealMajoranaCategory.cl11DoubledCore`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.Hurwitz.card_hurwitzDirections`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.Hurwitz.supercharge_sq_eq_laplacian`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/HurwitzRGFlow.lean`

- **`InfoGeometry.Quantum.HurwitzRGFlow.HurwitzShellAction.betaFunction_eq_zero_of_invariantAtScale`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/InvolutionCore.lean`

- **`InfoGeometry.Quantum.InvolutionCore.J_sq_apply`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Quantum.InvolutionCore.instAddCommGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Quantum.InvolutionCore.eps_sq_apply`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Quantum.InvolutionCore.instAddCommGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Quantum.InvolutionCore.je_def`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/KitaevChain.lean`

- **`InfoGeometry.Quantum.KitaevChain.KitaevCell.is_skew`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.KitaevChain.KitaevCocycle.cocycle`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.KitaevChain.hasDefect_singleton_iff_isCritical`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.KitaevChain.IsCritical`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.KitaevChain.index_change_forces_defect_crossing`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.KitaevChain.isCritical_iff_topologicalIndex_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.KitaevChain.kitaev_tiling_identity`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.KitaevChain.macroscopicVolume_eq_one_of_pfaffian_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.KitaevChain.macroscopicVolume_eq_prod_pfaffians`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.KitaevChain.topologicalIndexZ2_append_of_macroscopicVolume_ne_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.KitaevChain.topologicalIndex_eq_neg_one_or_one_of_macroscopicVolume_ne_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/ModularAnomaly.lean`

- **`InfoGeometry.Quantum.ModularAnomaly.Cl11LatticeBridge.coe_latticeAvatarCLM`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ModularAnomaly.Cl11LatticeBridge.instCompleteSpaceContinuousLinearMapRealIdContinuousCarrier`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.ModularAnomaly.Cl11LatticeBridge.ContinuousCarrier`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.ModularAnomaly.Cl11LatticeBridge.latticeAvatarCLM_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ModularAnomaly.Cl11LatticeBridge.latticeAvatar_exp_modularConjugationJ`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ModularAnomaly.Cl11LatticeBridge.latticeMatrixCLM_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ModularAnomaly.Cl11Shadow.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.ModularAnomaly.Cl11Shadow.modularAnomalyGenerator_eq_exp_commutator_shadow`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ModularAnomaly.Lattice.anomaly_free_blockA_is_orthogonal`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ModularAnomaly.Lattice.blockD_sigmaMatrix`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ModularAnomaly.Lattice.det_sigmaLDUProduct_eq_one_of_factorization`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.ModularAnomaly.Lattice.sigmaLDUProduct`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.ModularAnomaly.Lattice.invariant_parity_index`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.ModularAnomaly.Lattice.det_sigmaMatrix`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.ModularAnomaly.Lattice.latticeAnomalyCommutator_sigmaMatrix`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ModularAnomaly.Lattice.scalarBlock_eq_smul_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ModularAnomaly.Lattice.schurDet_sigmaMatrix`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ModularAnomaly.Lattice.thermal_berezinian_index`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ModularAnomaly.Lattice.wittenIndex_sigmaMatrix_eq_one_iff`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.ModularAnomaly.Lattice.wittenIndex_sigmaMatrix`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.ModularAnomaly.TopologicalMajoranaShadow.J_conj_sigma`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ModularAnomaly.TopologicalMajoranaShadow.einstein_anomaly_is_modular_generator`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.RealMajoranaCategory.RealMajoranaCore.V`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.ModularAnomaly.TopologicalMajoranaShadow.modularCocycle_zero`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.RealMajoranaCategory.RealMajoranaCore.V`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.ModularAnomaly.TopologicalMajoranaShadow.sigma_add`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/ProjectiveRayBridge.lean`

- **`InfoGeometry.Quantum.ProjectiveRayBridge.same_ray_incidence_left`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ProjectiveRayBridge.same_ray_incidence_right`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/RealKCategory.lean`

- **`InfoGeometry.Quantum.RealKCategory.RealKVect.Hom.comm`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealKCategory.RealKVect.Hom.ext_iff`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.RealKCategory.RealKVect.Hom`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.RealKCategory.RealKVect.K_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealKCategory.RealKVect.complexI_smul_eq_K`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealKCategory.RealKVect.hom_comp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealKCategory.RealKVect.hom_id`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/RealMajorana.lean`

- **`InfoGeometry.Quantum.RealMajorana.KPolarization.Hom.ext_iff`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.RealMajorana.KPolarization`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.RealMajorana.KPolarization.Hom.intertwines`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.KPolarization.K_maps_minus_to_plus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.KPolarization.K_maps_plus_to_minus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.KPolarization.P_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.KPolarization.PolarizationSplit.Hom.ext_iff`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.RealMajorana.KPolarization.PolarizationSplit.Hom.f`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.RealMajorana.KPolarization.PolarizationSplit.Hom.intertwines_minus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.KPolarization.PolarizationSplit.Hom.intertwines_plus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.KPolarization.PolarizationSplit.Hom.left_inv`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.KPolarization.PolarizationSplit.Hom.right_inv`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.KPolarization.PolarizationSplit.hom_comp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.KPolarization.PolarizationSplit.hom_id`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.KPolarization.creation_sub_annihilation_eq_P`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.RealMajorana.KPolarization`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.RealMajorana.KPolarization.hom_comp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.KPolarization.hom_id`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.KPolarization.ofSplit_splitOfPolarization_P`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.PolarizedMajorana.Hom.K_linear`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.PolarizedMajorana.Hom.Pi_even`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.PolarizedMajorana.Hom.ext_iff`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.RealMajorana.PolarizedMajorana.Hom`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.RealMajorana.PolarizedMajorana.Hom.gamma_intertwines`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.PolarizedMajorana.Hom.toBogoliubovTransform_preservesPolarization`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.RealMajorana.PolarizedMajorana`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.RealMajorana.PolarizedMajorana.hom_comp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.PolarizedMajorana.hom_id`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.PolarizedMajorana.ofPolarization_polarization`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.RealBogoliubovTransform.parity_even`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.RealBogoliubovTransform.preservesPolarization_iff_transportP_eq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.RealBogoliubovTransform.preserves_or_mixes`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.RealBogoliubovTransform.transportK_def`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.RealMajorana.RealBogoliubovTransform.B`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.RealMajorana.RealBogoliubovTransform.transportPi_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum.K_ne_Pi`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum.car_realization_of_clifford`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum.pairing`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum.chiralityPolarization_P`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum.chiralityPolarization_minus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum.chiralityPolarization_plus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/RealMajoranaCategory.lean`

- **`InfoGeometry.Quantum.RealMajoranaCategory.Polarization.involution_ofInvolution`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.RealMajoranaCategory.RealMajoranaCore.instModule`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.RealMajoranaCategory.Polarization.ofInvolution_involution_Pminus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajoranaCategory.Polarization.ofInvolution_involution_Pplus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajoranaCategory.PolarizedLadderRealization.compatible_minus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajoranaCategory.PolarizedLadderRealization.compatible_plus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajoranaCategory.PolarizedLadderRealization.minus_isotropic`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajoranaCategory.PolarizedLadderRealization.mixed_half`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajoranaCategory.PolarizedLadderRealization.plus_isotropic`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajoranaCategory.PolarizedMajorana.Hom.comm_Pminus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajoranaCategory.PolarizedMajorana.Hom.comm_Pplus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajoranaCategory.PolarizedMajorana.Hom.ext_iff`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.RealMajoranaCategory.PolarizedMajorana.Hom.homCore`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.RealMajoranaCategory.PolarizedMajorana.hom_comp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajoranaCategory.PolarizedMajorana.hom_id`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajoranaCategory.RealMajoranaCore.Hom.comm_Pi`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajoranaCategory.RealMajoranaCore.Hom.ext_iff`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.RealMajoranaCategory.RealMajoranaCore.instModule`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.RealMajoranaCategory.RealMajoranaCore.hom_comp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajoranaCategory.RealMajoranaCore.hom_id`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajoranaCategory.majorana_car_of_concrete_cl11`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.RealMajoranaCategory.cl11DoubledCore`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.RealMajoranaCategory.spectralMinusProj_comm_Pi`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajoranaCategory.spectralMinusProj_comp_spectralPlusProj`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajoranaCategory.spectralPlusProj_comm_Pi`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajoranaCategory.spectralPlusProj_comp_spectralMinusProj`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/RealSplitClifford.lean`

- **`InfoGeometry.Quantum.doubledSpaceCl11Action_J`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.doubledSpaceCl11Action_K`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.doubledSpaceCl11Action_eps`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.doubledSpaceCl11Action_eps_eq_cl11Rep_pseudoscalar`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/RosettaSynthesis.lean`

- **`InfoGeometry.Quantum.RosettaSynthesis.instCompleteSpaceVCl11DoubledCore`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.RealMajoranaCategory.cl11DoubledCore`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.RosettaSynthesis.rosetta_anomaly_free_triality`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RosettaSynthesis.rosetta_source_tension_synthesis`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/SplitCliffordAtom.lean`

- **`InfoGeometry.Quantum.SplitCliffordAtom.Atom.Hom.comm_eps`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.RealMajoranaCategory.RealMajoranaCore.instModule`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.SplitCliffordAtom.Atom.Hom.comm_j`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.RealMajoranaCategory.RealMajoranaCore.instModule`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.SplitCliffordAtom.Atom.Hom.comm_k`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.RealMajoranaCategory.RealMajoranaCore.instModule`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.SplitCliffordAtom.Atom.Hom.ext_iff`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.SplitCliffordAtom.Atom`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.SplitCliffordAtom.Atom.hom_comp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.SplitCliffordAtom.Atom.hom_id`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/TriadicBogoliubovBridge.lean`

- **`InfoGeometry.Quantum.TriadicBogoliubovBridge.dyadicKrein_apply`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instKreinSpaceProdL2`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Quantum/TriadicTransportBarycenter.lean`

- **`InfoGeometry.Quantum.TriadicTransport.HasUniqueSurprisalBarycenter.is_min`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.TriadicTransport.HasUniqueSurprisalBarycenter.nonzero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.TriadicTransport.HasUniqueSurprisalBarycenter.unique`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/TriadicTransportCore.lean`

- **`InfoGeometry.Quantum.TriadicTransport.TriadicTransportData.Addr_Probe_disjoint`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.TriadicTransport.TriadicTransportData.Addr_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.TriadicTransport.TriadicTransportData.Content_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.TriadicTransport.TriadicTransportData.Probe_Addr_disjoint`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.TriadicTransport.TriadicTransportData.Probe_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/TriadicTransportModular.lean`

- **`InfoGeometry.Quantum.TriadicTransport.modular_softMax_consistency`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.TriadicTransport.ExponentialModularTransport`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Quantum/TriadicTransportProjective.lean`

- **`InfoGeometry.Quantum.TriadicTransport.Update_content_proj_stable`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.TriadicTransport.Update_weight_proj_stable`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.TriadicTransport.TriadicTransportData.Update_weight_hom`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Quantum/TriadicWeylBridge.lean`

- **`InfoGeometry.Quantum.TriadicWeylBridge.dyadicKrein_isWeylCompatible_of_mem_minusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.TriadicWeylBridge.dyadicKrein_isWeylCompatible_of_mem_plusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.TriadicWeylBridge.eq_common_relative_form_of_scalarBlocks`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Quantum.TriadicWeylBridge.eq_logarithmicGenerator_of_scalarSheetBlocks`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.TriadicWeylBridge.eq_common_relative_form_of_scalarBlocks`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.TriadicWeylBridge.isWeylCompatible_iff_commutes_spectralMinusProj`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.TriadicWeylBridge.isWeylCompatible_iff_commutes_spectralPlusProj`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.instL2NormedGroup`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.TriadicWeylBridge.isWeylCompatible_iff_comp_spectralEpsilon`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.TriadicWeylBridge.triadicGenerator_blockDiagonal_of_compatibility`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/ZeroPointEnergy.lean`

- **`InfoGeometry.Quantum.ZeroPointEnergy.SpinFactorState.domain_valid`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ZeroPointEnergy.zero_point_energy_topological_obstruction`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.ZeroPointEnergy.zero_point_energy_positive`
  - Tags: `dead-candidate`, `wrapper-candidate`

## Most-Affected Files (top 20)

| File | Violations |
|------|------------|
| `lean/InfoGeometry/Quantum/RealMajorana.lean` | 42 |
| `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean` | 39 |
| `lean/InfoGeometry/Quantum/ModularAnomaly.lean` | 39 |
| `lean/InfoGeometry/Canonical/SinkhornFoundation.lean` | 36 |
| `lean/InfoGeometry/Canonical/MongeAmpereDualSheetBridge.lean` | 34 |
| `lean/InfoGeometry/Core/Involution.lean` | 32 |
| `lean/InfoGeometry/MaxEnt/Jaynes.lean` | 31 |
| `lean/InfoGeometry/Canonical/RicciMongeAmpere.lean` | 30 |
| `lean/InfoGeometry/Quantum/RealMajoranaCategory.lean` | 30 |
| `lean/InfoGeometry/Thermal/FiniteMatrix.lean` | 29 |
| `lean/InfoGeometry/Canonical/RestrictedSheetContinuous.lean` | 28 |
| `lean/InfoGeometry/Canonical/TomitaTakesaki.lean` | 27 |
| `lean/InfoGeometry/Krein/HilbertBridge.lean` | 27 |
| `lean/InfoGeometry/Krein/KreinSpace.lean` | 27 |
| `lean/InfoGeometry/Canonical/IBUpdate.lean` | 26 |
| `lean/InfoGeometry/Canonical/RestrictedVolumeCharacter.lean` | 23 |
| `lean/InfoGeometry/Geometry/DualFlat.lean` | 23 |
| `lean/InfoGeometry/ExponentialFamily/Analytic/LogSumExp.lean` | 22 |
| `lean/InfoGeometry/Canonical/BogoliubovTransport.lean` | 22 |
| `lean/InfoGeometry/Canonical/GrandCanonicalExperts.lean` | 22 |
