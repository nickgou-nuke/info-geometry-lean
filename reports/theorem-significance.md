# Declaration Vacuity Triage Report

**Declarations scored:** 7462  
**With violations:** 2740 (1889 error, 851 warning-only)  
**Clean:** 4722  

## Tag Distribution

| Tag | Count |
|-----|-------|
| `dead-candidate` | 4397 |
| `proof-infrastructure` | 2825 |
| `auto-generated` | 1773 |
| `certified-surface` | 411 |
| `statement-bearing` | 240 |
| `rfl-like` | 221 |
| `role-exempt` | 96 |
| `high-fan-in` | 93 |
| `wrapper-candidate` | 56 |
| `attr:infrastructure` | 38 |
| `attr:capstone` | 31 |
| `attr:expository` | 26 |
| `capstone-candidate` | 4 |
| `attr:terminal` | 1 |

## Violation Distribution

| Violation | Count |
|-----------|-------|
| `V2/dead-public-theorem` | 2686 |
| `V0/syntactic-vacuity` | 78 |
| `V1/public-wrapper-inflation` | 56 |
| `V4/bridge-infrastructure-promoted` | 3 |

## Top Vacuity Suspicion (derived ranking)

| Rank | Declaration | Suspicion | Confidence | Key Factors |
|------|---------|----------:|-----------:|-------------|
| 1 | `InfoGeometry.Canonical.Attention.polarizedSinkhornFinNonempty` | 0.8200 | 0.7940 | `shape.rfl-like`, `structure.low-descendant-mass`, `structure.low-public-fan-in` |
| 2 | `InfoGeometry.Canonical.PhaseSpaceConformalKKTBridge.toDoubledCopyRho_comp_phaseRotation_eq_KKT_dilationOperator` | 0.8100 | 0.8031 | `shape.exact-forward`, `structure.low-public-fan-in`, `structure.proof-only-reuse` |
| 3 | `InfoGeometry.Canonical.Attention.finNonempty` | 0.7900 | 0.8089 | `shape.rfl-like`, `structure.low-descendant-mass`, `structure.proof-only-reuse` |
| 4 | `InfoGeometry.Canonical.IB.pmf_normalize_eq_of_scale` | 0.7900 | 0.8089 | `shape.rfl-like`, `structure.low-descendant-mass`, `structure.proof-only-reuse` |
| 5 | `InfoGeometry.Quantum.KitaevChain.zero_exists_of_opposite_sign_symm` | 0.7900 | 0.8030 | `shape.exact-forward`, `structure.low-public-fan-in`, `structure.low-descendant-mass` |
| 6 | `InfoGeometry.Geometry.fenchelYoung_along_fderiv_of_concrete` | 0.7500 | 0.8096 | `shape.exact-forward`, `structure.low-public-fan-in`, `structure.low-descendant-mass` |
| 7 | `InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightPhaseAxis_eq_dilationOperator` | 0.7500 | 0.8027 | `shape.exact-forward`, `structure.low-public-fan-in`, `structure.shallow-depth` |
| 8 | `InfoGeometry.Quantum.KitaevChain.zero_exists_of_opposite_sign` | 0.7400 | 0.8020 | `shape.rfl-like`, `structure.low-descendant-mass`, `structure.low-public-fan-in` |
| 9 | `InfoGeometry.Math.Convexity.neg_log_jensen_sum` | 0.7300 | 0.8259 | `shape.exact-forward`, `structure.low-public-fan-in`, `structure.low-descendant-mass` |
| 10 | `InfoGeometry.Canonical.DensityWeightIntertwinerBridge.isCriticalDensityWeight_half` | 0.7300 | 0.7773 | `shape.rfl-like`, `structure.low-public-fan-in`, `structure.low-descendant-mass` |
| 11 | `InfoGeometry.Canonical.DensityWeightIntertwinerBridge.isCriticalDensityWeight_one` | 0.7300 | 0.7773 | `shape.rfl-like`, `structure.low-public-fan-in`, `structure.low-descendant-mass` |
| 12 | `InfoGeometry.Canonical.DensityWeightIntertwinerBridge.isCriticalDensityWeight_zero` | 0.7300 | 0.7773 | `shape.rfl-like`, `structure.low-public-fan-in`, `structure.low-descendant-mass` |
| 13 | `InfoGeometry.Twistor.Incidence.det_zero_of_annihilates_nonzero` | 0.7200 | 0.7925 | `shape.rfl-like`, `structure.low-descendant-mass`, `structure.low-public-fan-in` |
| 14 | `InfoGeometry.ExponentialFamily.Bernoulli.deriv_logPartition` | 0.7200 | 0.7849 | `shape.rfl-like`, `structure.low-public-fan-in`, `structure.low-descendant-mass` |
| 15 | `InfoGeometry.measurable_potential` | 0.7200 | 0.7849 | `shape.rfl-like`, `structure.low-public-fan-in`, `structure.low-descendant-mass` |
| 16 | `InfoGeometry.Canonical.AnomalyGauge.commutator_is_skew_adjoint` | 0.7100 | 0.7989 | `shape.rfl-like`, `structure.low-descendant-mass`, `structure.proof-only-reuse` |
| 17 | `InfoGeometry.Canonical.IB.pmf_normalize_apply_toReal` | 0.7100 | 0.7941 | `shape.rfl-like`, `structure.low-descendant-mass`, `structure.low-public-fan-in` |
| 18 | `InfoGeometry.Canonical.ManifoldDegree.exists_isolating_nhds_of_discrete` | 0.7100 | 0.7941 | `shape.rfl-like`, `structure.low-descendant-mass`, `structure.low-public-fan-in` |
| 19 | `InfoGeometry.Canonical.drazinDescriptorSystemsIsScalarTowerRealEndHEndH` | 0.7100 | 0.7941 | `shape.rfl-like`, `structure.low-descendant-mass`, `structure.low-public-fan-in` |
| 20 | `InfoGeometry.Canonical.drazinDescriptorSystemsSMulCommClassRealEndHEndH` | 0.7100 | 0.7941 | `shape.rfl-like`, `structure.low-descendant-mass`, `structure.low-public-fan-in` |

## Structural Metrics (top 20 by transitive reverse reach)

| Declaration | Reverse Reach | Descendant Mass | Depth | SCC Role | Public Fan-In | Proof-Only Reuse |
|---------|--------------:|----------------:|------:|----------|---------------:|-----------------:|
| `InfoGeometry.Krein.DoubledSpace.ext` | 935 | 1 | 16 | `acyclic` | 0 | 147 |
| `InfoGeometry.Krein.instL2Complete` | 864 | 0 | 14 | `acyclic` | 246 | 119 |
| `InfoGeometry.PositiveMeasure.pos` | 450 | 2 | 26 | `acyclic` | 0 | 24 |
| `InfoGeometry.Canonical.CertifiedInverseKernel.toInverseKernel` | 422 | 2 | 18 | `acyclic` | 33 | 26 |
| `InfoGeometry.Canonical.CertifiedInverseKernel.toInverseKernel'` | 395 | 3 | 17 | `acyclic` | 3 | 39 |
| `InfoGeometry.Projective.positiveMeasureToEuclidean_apply` | 394 | 3 | 26 | `acyclic` | 0 | 2 |
| `InfoGeometry.Projective.positiveMeasureToEuclidean_ne_zero` | 393 | 5 | 25 | `acyclic` | 0 | 4 |
| `InfoGeometry.PositiveMeasure.ext` | 392 | 6 | 22 | `acyclic` | 0 | 8 |
| `InfoGeometry.Projective.positiveMeasureToEuclidean_scale` | 391 | 5 | 24 | `acyclic` | 0 | 1 |
| `InfoGeometry.Projective.positiveMeasureToConeInteriorRay_sameRay` | 390 | 17 | 23 | `acyclic` | 0 | 1 |
| `InfoGeometry.Projective.projectiveClassToConeInteriorStateSpace_injective` | 383 | 25 | 21 | `acyclic` | 0 | 1 |
| `InfoGeometry.Projective.projectiveClassToConeInteriorStateSpace_surjective` | 383 | 22 | 21 | `acyclic` | 0 | 1 |
| `InfoGeometry.Projective.projectiveClassToConeInteriorStateSpace_bijective` | 382 | 28 | 20 | `acyclic` | 0 | 1 |
| `InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.toConformalInference` | 326 | 2 | 18 | `acyclic` | 135 | 14 |
| `InfoGeometry.Krein.complex_i_apply` | 316 | 6 | 15 | `acyclic` | 0 | 95 |
| `InfoGeometry.Krein.modular_j_involution` | 245 | 4 | 12 | `acyclic` | 1 | 9 |
| `InfoGeometry.Canonical.CertifiedInverseKernel.spectralProjector` | 244 | 8 | 16 | `acyclic` | 33 | 23 |
| `InfoGeometry.Krein.spectral_epsilon_involution` | 236 | 4 | 12 | `acyclic` | 1 | 9 |
| `InfoGeometry.Canonical.CertifiedInverseKernel.metricProjector` | 196 | 8 | 15 | `acyclic` | 23 | 13 |
| `InfoGeometry.Krein.modular_j_spectral_epsilon_anticommute` | 186 | 5 | 11 | `acyclic` | 1 | 7 |

## Errors (require action)

### `lean/InfoGeometry/Canonical/AQFTOperatorEndpoints.lean`

- **`InfoGeometry.Canonical.AQFTOperatorInterface.ibWeightedKMSClosure_of_jointKernel_commutator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

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

### `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean`

- **`InfoGeometry.Canonical.AlgebraicStationarity.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AlgebraicStationarity.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AlgebraicStationarity.isAlgebraicallyStationary_iff`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AlgebraicStationarity.isAlgebraicallyStationary_of_central`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AlgebraicStationarity.isAlgebraicallyStationary_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AlgebraicStationarity.isStateAlgebraicallyStationary_iff_algebraicEinsteinBalance`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AlgebraicStationarity.isStateAlgebraicallyStationary_iff_generatorStationarity`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AlgebraicStationarity.isStationaryAlong_iff`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AlgebraicStationarity.modularCurvatureExpectation_eq_zero_of_phaseResponseStationary`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AlgebraicStationarity.operatorInformationFirstVariation_neg_left`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AlgebraicStationarity.operatorInformationFirstVariation_neg_right`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AlgebraicStationarity.phaseAxisResponse_eq_neg_KVariation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AlgebraicStationarity.starCertifiedEinsteinAnomalyStationary_iff_projectorObstructionStationary_of_projectorAgreement`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`

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

- **`InfoGeometry.Canonical.AnalyticalIndex.KRotationLE_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.KRotationLE_symm_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex_eq_of_chiralParts_eq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex_eq_zero_time_of_cartanConjugate`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.chiralPartMinus_eq_projectorPlus_comp_of_anticommute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.chiralPartPlus_eq_projectorMinus_comp_of_anticommute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.chiralProjectorMinus_comp_self_of_square_eq_id`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.chiralProjectorPlus_comp_self_of_square_eq_id`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.chiralSliceIsoAlong_of_noZeroEigenCrossing_path`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.cl11BottAnalyticalIndex_eq_neg_of_projectiveJ`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.cl11BottAnalyticalIndex_eq_zero_time_of_conjugacy`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.cl11BottDirac_comp_cl11GlobalGrading_add_cl11GlobalGrading_comp_cl11BottDirac`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.cl11_bottDirac_sq_eq_zero_of_dirac_sq_eq_neg_id`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.cl11_bottDirac_sq_eq_zero_of_laplacian_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AnalyticalIndex.indexInvariantAlong_of_noZeroEigenCrossing_path`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/AnomalyGauge.lean`

- **`InfoGeometry.Canonical.AnomalyGauge.anomaly_generates_isometry`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/AnomalyInflow.lean`

- **`InfoGeometry.Canonical.AnomalyInflow.anomalyInflowClosure`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean`

- **`InfoGeometry.Canonical.MoE.arnoldNetwork_preserves_base`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.arnoldNetwork_preserves_transportWeylMinus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.arnoldNetwork_preserves_transportWeylMinus_and_ker_of_linearExperts_commuting`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.arnoldNetwork_preserves_transportWeylMinus_nonzero_ker_of_experts_fix`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.arnoldNetwork_preserves_transportWeylMinus_of_linearExperts_commute_transportJ`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.arnoldNetwork_preserves_transportWeylPlus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.arnoldNetwork_preserves_transportWeylPlus_and_ker_of_linearExperts_commuting`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.arnoldNetwork_preserves_transportWeylPlus_nonzero_ker_of_experts_fix`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.arnoldNetwork_preserves_transportWeylPlus_of_linearExperts_commute_transportJ`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.exists_network_fixed_transportWeylMinus_nonzero_ker_of_experts_fix_of_simplifiedBoundaryModel_under_bogoliubov`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.exists_network_fixed_transportWeylMinus_nonzero_ker_of_experts_fix_of_weylZeroModePair`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.exists_network_fixed_transportWeylPlus_nonzero_ker_of_experts_fix_of_simplifiedBoundaryModel_under_bogoliubov`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.exists_network_fixed_transportWeylPlus_nonzero_ker_of_experts_fix_of_weylZeroModePair`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/AttentionEuclidean.lean`

- **`InfoGeometry.Canonical.Attention.euclideanAttentionWeights_sum_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/AttentionPolarizedGibbsBridge.lean`

- **`InfoGeometry.Canonical.Attention.partition_polarizedPlusParams_eq_logitSum`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Attention.polarizedPlusAttentionHead_eq_gibbsExpectation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Attention.polarizedPlusAttentionWeights_eq_euclideanGibbsWeights_of_constantKeyNorm`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Attention.polarizedPlusParams_energy`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Attention.polarizedPlusParams_energy_eq_neg_dot_plus_half_norms`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/AttentionPolarizedSinkhornBridge.lean`

- **`InfoGeometry.Canonical.Attention.exists_perm_decomposition_of_bistochastic_polarizedPlusAttention`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Attention.polarizedPlusAttentionMatrix_mem_rowStochastic`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/AttentionPolarizedSplit.lean`

- **`InfoGeometry.Canonical.Attention.polarizedPlusAttentionHead_eq_euclideanAttentionHead_of_constantKeyNorm`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Attention.polarizedPlusAttentionWeights_sum_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/AttentionSplit.lean`

- **`InfoGeometry.Canonical.Attention.lorentzianAttentionWeights_sum_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/BekensteinBound.lean`

- **`InfoGeometry.Canonical.BekensteinBound.cocycleIncrement_abs_le_trajectoryRNBarrier_of_connesCocycle_generatorLift`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BekensteinBound.relEnt_drop_nonneg_of_casiniIncrementBridge`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BekensteinBound.topologicalBekensteinBound_of_connesCocycle`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BekensteinBound.topologicalBekensteinBound_of_connesCocycle_natMatch`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BekensteinBound.topologicalBekensteinBound_of_tomitaConnesCocycle_generatorLift`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/BeliefAlgebra.lean`

- **`InfoGeometry.Canonical.BeliefAlgebra.BeliefSystem.non_commutative_updates`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/BeliefDynamics.lean`

- **`InfoGeometry.Canonical.BeliefDynamics.parallelTransportE_eq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BeliefDynamics.parallelTransportM_eq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BeliefDynamics.quantumGeometryOp_eq_metricOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BeliefDynamics.radonNikodymOp_pos`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/BerryConnection.lean`

- **`InfoGeometry.Canonical.BerryPhase.SuperHestenesKaehlerDatum.BigradedSuperHestenesDatum.J_phase_odd`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.SuperHestenesKaehlerDatum.BigradedSuperHestenesDatum.K_phase_even`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.SuperHestenesKaehlerDatum.BigradedSuperHestenesDatum.epsilon_phase_odd`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.SuperHestenesKaehlerDatum.BigradedSuperHestenesDatum.fermionic_surface`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.SuperHestenesKaehlerDatum.JBoost_add`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.SuperHestenesKaehlerDatum.JBoost_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.SuperHestenesKaehlerDatum.J_anticomm_epsilon`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.SuperHestenesKaehlerDatum.J_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.SuperHestenesKaehlerDatum.KRotation_add`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.SuperHestenesKaehlerDatum.KRotation_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.SuperHestenesKaehlerDatum.K_eq_J_comp_epsilon`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.SuperHestenesKaehlerDatum.K_eq_modularComplexI`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.SuperHestenesKaehlerDatum.K_sq_neg`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.SuperHestenesKaehlerDatum.epsilonBoost_add`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.SuperHestenesKaehlerDatum.epsilonBoost_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.SuperHestenesKaehlerDatum.epsilon_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.SuperHestenesKaehlerDatum.ofQGT_J`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.SuperHestenesKaehlerDatum.ofQGT_K`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.SuperHestenesKaehlerDatum.ofQGT_epsilon`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.SuperHestenesKaehlerDatum.ofQGT_metric`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.SuperHestenesKaehlerDatum.ofQGT_phase`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.SuperHestenesKaehlerDatum.phase_eq_metric_of_K`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.SuperHestenesKaehlerDatum.toQGT_berry`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.SuperHestenesKaehlerDatum.toQGT_metric`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.deriv_berryOfOperator_phaseAxisTransport_at_zero_eq_berryOf_two_smul_comp_modularComplexI_of_IsPhaseAntilinear`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.deriv_hestenesWeylModularBerryTransport_at_eq_berryOf_hestenesWeylConnectionGenerator_add_relativeModularSourceDeriv_of_commute_gaugePart`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.deriv_hestenesWeylModularBerryTransport_at_zero_eq_hestenesWeylModularBerryTwoForm`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.hestenesBerryTwoForm_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.hestenesMaurerCartanCurvature_skew`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.hestenesWeylModularBerryTwoForm_eq_berryOf_hestenesWeylConnectionGenerator_add_relativeModularSourceDeriv_of_commute_gaugePart`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BerryPhase.starCertifiedEinsteinAnomalyQGT_berry_eq_metricOfOperator_liftedProjectorObstructionOperator_of_projectorAgreement`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`

### `lean/InfoGeometry/Canonical/BogoliubovClosedForms.lean`

- **`InfoGeometry.Canonical.BogoliubovClosedForms.JBoost_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovClosedForms.epsilon_comp_JBoost`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovClosedForms.epsilon_comp_KRotation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovClosedForms.epsilon_comp_epsilonBoost`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovClosedForms.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/BogoliubovFockSuper.lean`

- **`InfoGeometry.Canonical.BogoliubovFockSuper.HyperbolicMixingParams.normalization`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.anticommutator_bogoliubov_eq_zero_of_coeff_eq_inducedChemicalPotential_of_vacuumTransported`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.anticommutator_ofAngle_projector_model`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.bogoliubovAnnihilation_kills_vacuumVector`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.bogoliubovCreation_kills_vacuumVector`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.car_realization_of_clifford`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.cliffordConcreteAnnihilation_apply_to_doubled`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.cliffordConcreteCreation_apply_to_doubled`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.commutator_annihilation_self`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.commutator_creation_self`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.fockAnticommutator_symm`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.fockCommutator_swap`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.inducedChemicalPotential_eq_zero_of_vacuumTransported`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.not_isCARPair_base`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovFockSuper.projectorSuperPair_of_chiralityPolarization`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/BogoliubovPolarizationBridge.lean`

- **`InfoGeometry.Canonical.BogoliubovPolarizationBridge.bogoliubovPolarizationBridge_of_strictSymmetry`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovPolarizationBridge.car_realization_of_strictSymmetryBogoliubov`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/BogoliubovProjectorFlux.lean`

- **`InfoGeometry.Canonical.BogoliubovProjectorFlux.minusProjectorFlux_JBoost`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorFlux.minusProjectorFlux_KRotation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorFlux.plusProjectorFlux_JBoost`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorFlux.plusProjectorFlux_KRotation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorFlux.transportedMinusProjector_JBoost`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorFlux.transportedMinusProjector_KRotation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorFlux.transportedMinusProjector_epsilonBoost`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorFlux.transportedPlusProjector_JBoost`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorFlux.transportedPlusProjector_KRotation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorFlux.transportedPlusProjector_epsilonBoost`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/BogoliubovProjectorTransport.lean`

- **`InfoGeometry.Canonical.BogoliubovProjectorTransport.epsilonBoost_preserves_minusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorTransport.epsilonBoost_preserves_plusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorTransport.modularComplexI_maps_minusSheet_to_plusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorTransport.modularComplexI_maps_plusSheet_to_minusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorTransport.modularConjugationJ_maps_minusSheet_to_plusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorTransport.modularConjugationJ_maps_plusSheet_to_minusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorTransport.modularTransportFlow_deriv`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovProjectorTransport.spectralPlusProj_comp_modularTransportFlow`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/BogoliubovTransport.lean`

- **`InfoGeometry.Canonical.BogoliubovTransport.deriv_KRotation_transport_at_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.deriv_modularTransport_conjugation_eq_expTransport_potentialChanging_of_commute_potentialPreserving`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.deriv_modularTransport_conjugation_eq_expTransport_potentialPreserving_add_expTransport_potentialChanging`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.heisenbergKreinTransport_split_generator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.modularTransportFlow_add`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.modularTransportFlow_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.modularVariance_of_normalized`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.neg_phaseConjugate_comp_phaseAxis`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.phaseAxisForce_add`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.phaseAxisForce_smul`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.phaseAxisTransport_eq_from_phaseAntilinearPart`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.phaseAxisTransport_eq_zero_of_IsPhaseLinear`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovTransport.relativeModularPotentialChangingDeriv_add_relativeModularSinkDeriv`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/BogoliubovVielbein.lean`

- **`InfoGeometry.Canonical.BogoliubovVielbein.BogoliubovVielbeinBundle.bianchi_identity`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovVielbein.BogoliubovVielbeinBundle.deriv_localFrame_at`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovVielbein.BogoliubovVielbeinBundle.deriv_localFrame_at_eq_transportedMaurerCartanCurvature`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovVielbein.BogoliubovVielbeinBundle.deriv_localFrame_at_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/BohmMadelungOperatorialBridge.lean`

- **`InfoGeometry.Canonical.BohmMadelungOperatorialBridge.constantStateGeneratorField_generator_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BohmMadelungOperatorialBridge.constantStateGeneratorField_phaseAxisForce_eq_from_stateSourceGenerator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BohmMadelungOperatorialBridge.constantStateGeneratorField_phaseAxisResponse_stateGaugeGenerator_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BohmMadelungOperatorialBridge.constantStateGeneratorField_phaseAxisResponse_stateSourceGenerator_eq_two_smul_comp_K`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BohmMadelungOperatorialBridge.constantStateGeneratorField_stateInducedDerivation_eq_phaseLinear_add_phaseAntilinear_transport`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BohmMadelungOperatorialBridge.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BohmMadelungOperatorialBridge.polarizedDoubledAmplitude_modularConjugationJ_phaseOrbit_eq_reverse`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BohmMadelungOperatorialBridge.polarizedDoubledAmplitude_phaseOrbit_eq_dilationOrbit`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BohmMadelungOperatorialBridge.potentialDatum_constantStateGeneratorField_kSplitReadout_stationary_iff_isPotentialKillingOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BohmMadelungOperatorialBridge.stateGeneratorField_phaseReadout_eq_metric_comp_K`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/BottDirac.lean`

- **`InfoGeometry.Canonical.BottDirac.bottDirac_apply_tmul`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BottDirac.bottDirac_sq_eq_sum_laplacians`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BottDirac.cl11_bottDirac_sq_apply_tmul`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BottDirac.cl22_bottDirac_sq_eq_two_tensor_id`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BottDirac.spectralDiracLinear_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/BottPeriodicity.lean`

- **`InfoGeometry.Canonical.BottPeriodicity.bottStepEquiv_symm_left_generator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BottPeriodicity.bottStepEquiv_symm_right_generator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BottPeriodicity.firstBottStep_consumes_doubledSpaceCl11Action_J`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BottPeriodicity.firstBottStep_consumes_doubledSpaceCl11Action_K`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BottPeriodicity.gradedProdInjection_matches_pattern_unit`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
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

### `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean`

- **`InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.exists_zeroMode_and_nontrivial_regularization_pair_of_dim_mismatch`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/CalabiYauMetricRicci.lean`

- **`InfoGeometry.Canonical.CalabiYauBridge.vacuumEinsteinEquation_of_unitRelativeVolume`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/CalabiYauRNMongeAmpere.lean`

- **`InfoGeometry.Canonical.CalabiYauBridge.absDet_cramerRaoMetric_eq_one_of_rnEntropySource_of_unitRelativeVolume`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CalabiYauBridge.logAbsDet_cramerRaoMetric_eq_zero_of_rnEntropySource_of_unitRelativeVolume`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CalabiYauBridge.log_mongeAmpereDensity_eq_neg_kahlerPotentialRN_of_rnEntropySource`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CalabiYauBridge.rnEntropySourcesMongeAmperePotential_of_logF_eq_neg_kahlerPotentialRN`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/CalabiYauSingularBridge.lean`

- **`InfoGeometry.Canonical.CalabiYauSingularTransportBridge.isRicciFlat_and_logDivergence_eq_projective_nilpotent_graded_of_unitRelativeVolume_metricDerived_of_boundaryScale_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CalabiYauSingularTransportBridge.isRicciFlat_and_logDivergence_eq_singularComplement_of_unitRelativeVolume_metricDerived`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CalabiYauSingularTransportBridge.vacuumEinsteinEquation_and_logDivergence_eq_projective_nilpotent_graded_of_unitRelativeVolume_metricDerived_of_boundaryScale_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CalabiYauSingularTransportBridge.vacuumEinsteinEquation_and_logDivergence_eq_singularComplement_of_unitRelativeVolume_metricDerived`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/CanonicalGaugeBridge.lean`

- **`InfoGeometry.Canonical.CanonicalGaugeBridge.comparisonGeneratorMetric_referenceInvariant`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CanonicalGaugeBridge.comparisonGeneratorPhase_referenceInvariant`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CanonicalGaugeBridge.comparisonInducedDynamics_referenceInvariant`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CanonicalGaugeBridge.comparisonTransportGenerator_referenceInvariant`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CanonicalGaugeBridge.firstVariation_referenceInvariant`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CanonicalGaugeBridge.functionalShift_reference_cocycle`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CanonicalGaugeBridge.functionalShift_self_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/CartanBerezinianCore.lean`

- **`InfoGeometry.Canonical.CartanBerezinianCore.generalizedBerezinianScale_eq_restrictedVolumeScale`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CartanBerezinianCore.generalizedBerezinian_diagonal_reduction`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/CartanDecomposition.lean`

- **`InfoGeometry.Canonical.CartanDecomposition.InformationCartanTriple.grading_commutator_anomaly`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CartanDecomposition.InformationCartanTriple.mul_spectralGradingFlow_eq_spectralGradingFlow_neg_mul_of_anticommute_GammaS`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CartanDecomposition.InformationCartanTriple.spectralAdjointFlow_mem_compact`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CartanDecomposition.InformationCartanTriple.spectralCommutator_compact_noncompact`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CartanDecomposition.InformationCartanTriple.spectralCommutator_mem_compact`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CartanDecomposition.InformationCartanTriple.spectralCommutator_mem_compact_of_noncompact`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CartanDecomposition.InformationCartanTriple.spectralGradingFlow_mem_compact`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CartanDecomposition.InformationCartanTriple.spectral_proj_is_compact_of_normal`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/CayleyBregmanBridge.lean`

- **`InfoGeometry.Canonical.Cayley.Bridge.left_inv`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Cayley.Bridge.right_inv`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Cayley.cayleyNegationPythagoreanInvariance`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Cayley.cayleyPythagoreanInvariance`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Cayley.grad_transport_back`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Cayley.quadraticDualFlat_divergence`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Cayley.quadraticDualFlat_nabla`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean`

- **`InfoGeometry.Canonical.CertifiedInverseKernel.chiralAnomaly_eq_mismatch_commutator_metric`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.chiralAnomaly_spectralAdjointFlow_mem_noncompact`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.chiralScale_eq_zero_iff_chiralAnomaly_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.projectorMismatch_eq_zero_iff`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.rightChiralAnomaly_eq_chiralAnomaly_of_projectorAgreement`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.rightChiralAnomaly_spectralAdjointFlow_mem_noncompact`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.spectralProjector_commutator_spectralAdjointFlow_dilationGap_eq_mul_spectralGradingFlow_neg_two`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.instIsScalarTowerRealContinuousLinearMapId_infoGeometry`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`, `rfl-like`
- **`InfoGeometry.Canonical.instSMulCommClassRealContinuousLinearMapId_infoGeometry`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`, `rfl-like`

### `lean/InfoGeometry/Canonical/ChiralAction.lean`

- **`InfoGeometry.Canonical.ChiralAction.chiralDirac_eq_of_unitRelativeVolume`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ChiralAnomaly.lean`

- **`InfoGeometry.Canonical.ChiralAnomaly.exists_routingEpsilon_of_mem_doublyStochastic`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ChiralAnomaly.normal_inverse_anomaly_vanishes`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ChiralAnomaly.routingEpsilon_eq_semantic_gap_abs`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ChiralAnomaly.sinkhornIterate_generator_step_control`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ChiralAnomaly.sinkhornIterate_step_control`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ChiralAnomaly.sinkhornPermutationWeights_decomposition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ChiralEinsteinBridge.lean`

- **`InfoGeometry.Canonical.ChiralEinsteinBridge.anomalyDrivenScalarRicci_fixedpoint_tracks_source`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ChiralEinsteinBridge.anomalyDriven_fixedpoint_eq_inverseEpsilon`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ChiralEinsteinBridge.anomalyDriven_zeroSource_iff_normalized`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ChiralEinsteinBridge.anomalyStressEnergyAt_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ChiralEinsteinBridge.anomalyStressEnergyAt_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ChiralEinsteinBridge.exists_einsteinEquation_of_bistochastic_routingAnomaly`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ChiralGravity.lean`

- **`InfoGeometry.Canonical.ChiralGravity.anomalyEinsteinResidualAt_def`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ChiralGravity.anomaly_nonzero_excludes_vacuum`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ChiralGravity.routingAnomaly_nonzero_forces_curved_plus_component`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ChiralRGFlow.lean`

- **`InfoGeometry.Canonical.ChiralRGFlow.ChiralAsymptoticModel.beta_eq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ChiralRGFlow.ChiralAsymptoticModel.gamma_pos`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ChiralRGFlow.asymptotic_freedom_of_negative_beta`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ChiralTorsionGeneralizedKL.lean`

- **`InfoGeometry.Canonical.ChiralTorsionBridge.gibbsSmoothingOnGeneralizedKL_nonneg`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ChiralTorsionState.lean`

- **`InfoGeometry.Canonical.ChiralTorsionBridge.chentsov_and_gibbs_of_state`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ChiralTorsionBridge.torsion_nonzero_of_state_and_chiral`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ChiralTorsionBridge.twistedInference_torsion_nonzero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ClNNBottBridge.lean`

- **`InfoGeometry.Canonical.ClNNBottBridge.bottStep_headNullMinus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ClNNBottBridge.bottStep_headNullPlus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ClNNBottBridge.bottStep_tailLift`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/CliffordBridge.lean`

- **`InfoGeometry.Canonical.CliffordBridge.splitBilinear_eq_gaugeBilinear`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.CliffordBridge.B_agrees_with_Gauge_bilinear`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.CliffordBridge.splitQuadratic_eq_gaugeQuadratic`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.CliffordBridge.q_agrees_with_Gauge_quad`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/CoarseGraining.lean`

- **`InfoGeometry.Canonical.encoderMarginal_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ConformalAlgebra.lean`

- **`InfoGeometry.Canonical.ConformalAlgebra.ConformalBeliefAlgebra.D_eq_CI_D`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
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
- **`InfoGeometry.Canonical.ConformalAlgebra.ConformalBeliefAlgebra.scale_anomaly_obstructs_weyl_flatness`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ConformalAnomalyDegenerate.lean`

- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.NormalPhaseDegeneratePackage.chiralScale_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.NormalPhaseDegeneratePackage.isNormalInference`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.NormalPhaseDegeneratePackage.projectorObstruction_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.NormalPhaseDegeneratePackage.projectors_commute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.normalPhaseDegeneratePackage_of_kahlerLogDet_unitRelativeVolume`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ConformalAnomalyOperator.lean`

- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.ObstructionOperatorOwner.obstruction_diagonal_blocks`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.ObstructionOperatorOwner.obstruction_eq_commutator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.ObstructionOperatorOwner.obstruction_isGZero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.ObstructionOperatorOwner.obstruction_minusProjector_mul_mul_plusProjector_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.ObstructionOperatorOwner.obstruction_plusProjector_mul_mul_minusProjector_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.SquashedObstructionOperatorOwner.squashedObstruction_diagonal_blocks`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.SquashedObstructionOperatorOwner.squashedObstruction_isGZero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.SquashedObstructionOperatorOwner.squashedObstruction_minusProjector_mul_mul_plusProjector_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.SquashedObstructionOperatorOwner.squashedObstruction_plusProjector_mul_mul_minusProjector_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.dilationSource_eq_neg_half_projectorObstruction_of_rightProjector_commute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.dilationSource_eq_neg_half_projectorObstruction_of_structuredProjectorHypotheses`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.obstructionOperatorOwner_of_kkt_wings`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.squashedObstructionOperatorOwner_of_kkt_wings`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ConformalAnomalyReadout.lean`

- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.ObstructionScalarReadout.chiralScale_eq_obstructionScale`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.ObstructionScalarReadout.epsilon_eq_obstructionScale`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.ObstructionScalarReadout.obstructionScale_eq_projectorObstruction_nnnorm`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.ObstructionScalarReadout.projectorObstruction_nnnorm_eq_obstructionScale`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.ObstructionScalarReadout.unitOfAction_eq_obstructionScale`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.ObstructionScalarReadout.unitOfAction_eq_projectorObstruction_nnnorm`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.obstructionScalarReadout`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ConformalAnomalySource.lean`

- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.chiralAnomalyOperator_eq_zero_of_unitRelativeVolume`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.chiralAnomaly_eq_zero_of_kahlerLogDet_normalized_fixedpoint`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.chiralScale_eq_projectorObstruction_norm`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.chiralScale_ne_zero_of_projectors_not_commute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.einsteinEquation_of_projectorObstruction_source`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.isChiralInference_iff_epsilon_pos`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.isNormalInference_iff_epsilon_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.isNormalInference_of_logDetBarrier_selfConcordance_mechanics`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.projectorObstructionSquashCoeff_eq_squashedObstructionScale_div_obstructionScale`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.projectorObstructionSquashCoeff_eq_zero_of_obstructionScale_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.projectorObstructionSquashCoeff_mul_obstructionScale_eq_squashedObstructionScale`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.projectorObstruction_eq_zero_iff_commute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.spectralProjector_commutator_dilation_eq_zero_of_rightProjector_commute_of_chiralScale_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.spectralProjector_commutator_dilation_eq_zero_of_rightProjector_commute_of_projectorObstruction_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.squashedObstructionScale_eq_tanh_obstructionScale`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.squashedProjectorObstruction_eq_smul_projectorObstruction`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.squashedProjectorObstruction_eq_zero_of_obstructionScale_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.unitOfAction_pos_of_chiralInference`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.unitOfAction_pos_of_noncommute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ConformalProjectorCore.lean`

- **`InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.leftChiralAnomalyOperator_star_eq_neg_of_isSelfAdjoint`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.metricProjector_idempotent`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.mpRangeProjector_idempotent`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.projectorObstructionOperator_eq_chiralAnomalyOperator`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.projectorObstructionOperator_eq_leftChiralAnomalyOperator`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.rightChiralAnomalyOperator_star_eq_neg_of_isSelfAdjoint`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.spectralProjector_idempotent`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.spectralProjector_isSelfAdjoint_of_isSelfAdjoint`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.specialConformal_eq_modularInversion_translation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.spectralProjector_commutator_dilation_eq_neg_half_einstein_plus_chiral`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.spectralProjector_commutator_dilation_eq_neg_half_leftChiralAnomaly_of_rightProjector_commute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.spectralProjector_commutator_dilation_eq_zero_of_rightProjector_commute_of_leftChiralAnomaly_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ConformalInference.translation_eq_modularInversion_specialConformal`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.ProjectorAgreementCertifiedConformalInference.rightChiralAnomaly_eq_chiralAnomaly`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`

### `lean/InfoGeometry/Canonical/ConnesArakiCore.lean`

- **`InfoGeometry.Canonical.ConnesArakiFramework.ArakiRelativeEntropyRestrictionDropMonotone.drop_abs_le`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ConnesArakiTomita.lean`

- **`InfoGeometry.Canonical.ConnesArakiFramework.abs_squeezingLogShear_le_of_abs_time_le_tomitaArakiRelativeEntropyDrop`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ConnesArakiFramework.topologicalBekensteinBound_and_tomitaModularKMS_of_tomitaConnesArakiData`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/CoordinateFreeSecondVariation.lean`

- **`InfoGeometry.Canonical.CoordinateFreeSecondVariation.comparisonState_metric_phase_pair_eq_correlation_pair`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CoordinateFreeSecondVariation.modularCurvatureOperator_eq_metricPart_phaseAxis`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CoordinateFreeSecondVariation.operatorInformationCurvaturePart_self_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CoordinateFreeSecondVariation.toRelationalInformationDatum_comparisonMetricPhaseReadout_pair_eq_gauge_source_operator_pair`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CoordinateFreeSecondVariation.toRelationalInformationDatum_comparisonMetricPhaseReadout_pair_eq_operator_pair`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CoordinateFreeSecondVariation.toRelationalInformationDatum_metric_phase_pair_eq_correlation_pair`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/CorrelationAntisymmetrization.lean`

- **`InfoGeometry.Canonical.CorrelationAntisymmetrization.antisymmetricPhaseShiftedTwoStateChannelCorrelation_swap_neg`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CorrelationAntisymmetrization.comparisonStateGeneratorPhase_eq_antisymmetricPhaseShiftedTwoStateChannelCorrelation_self_of_IsPhaseLinear`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CorrelationAntisymmetrization.phaseShiftedTwoStateChannelCorrelation_eq_symmetric_add_antisymmetric`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CorrelationAntisymmetrization.symmetricPhaseShiftedTwoStateChannelCorrelation_self_eq_zero_of_IsPhaseLinear`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CorrelationAntisymmetrization.symmetricPhaseShiftedTwoStateChannelCorrelation_swap`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CorrelationAntisymmetrization.toRelationalInformationDatum_comparisonGeneratorPhase_eq_antisymmetricPhaseShiftedTwoStateChannelCorrelation_self_of_IsPhaseLinear`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/CorrelationSymmetrization.lean`

- **`InfoGeometry.Canonical.CorrelationSymmetrization.antisymmetricTwoStateChannelCorrelation_self_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CorrelationSymmetrization.antisymmetricTwoStateChannelCorrelation_swap_neg`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CorrelationSymmetrization.symmetricTwoStateChannelCorrelation_swap`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CorrelationSymmetrization.twoStateChannelCorrelation_eq_symmetric_add_antisymmetric`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/CountPositiveCoupling.lean`

- **`InfoGeometry.Canonical.CountSubstrateBridge.countInducedPositiveIterate.colNormalize_entrywisePositive`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CountSubstrateBridge.countInducedPositiveIterate.rowNormalize_entrywisePositive`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/CountProbabilityState.lean`

- **`InfoGeometry.Canonical.CountSubstrateBridge.empiricalProbabilityState_spec`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/CountSinkhornFlow.lean`

- **`InfoGeometry.Canonical.CountSubstrateBridge.emergentTimeFlow_countInducedSinkhornTrajectory`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/DensityWeightIntertwinerBridge.lean`

- **`InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedModularSeed_eq_transportGenerator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedReadout_zero_apply_eq_metricPhase_transportCommutator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightLiftedTransportGenerator_eq_souriau_add_weighted_dilation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightPhaseAxis_eq_dilationOperator`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_eq_dilationOperator`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightPhaseAxis_eq_modularComplexI`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightWeylIntertwiners_of_strictSymmetry_fst`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightWeylIntertwiners_of_strictSymmetry_snd`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DensityWeightIntertwinerBridge.isCriticalDensityWeight_half`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`, `rfl-like`
- **`InfoGeometry.Canonical.DensityWeightIntertwinerBridge.isCriticalDensityWeight_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`, `rfl-like`
- **`InfoGeometry.Canonical.DensityWeightIntertwinerBridge.isCriticalDensityWeight_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`, `rfl-like`
- **`InfoGeometry.Canonical.DensityWeightIntertwinerBridge.projectiveDensityWeightHamiltonianProfile_eq_relativeModularPotential_countRay_add_weightShift`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DensityWeightIntertwinerBridge.projectiveDensityWeightHamiltonianProfile_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/Determinant.lean`

- **`InfoGeometry.Canonical.Determinant.linearEquivLogGenerator_eq_logAbsVolume`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Determinant.linearEquivLogGenerator_mul`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

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
- **`InfoGeometry.Canonical.DiagonalMetricModularBridge.spectral_dirac_sq_apply_eq_relativeModularHamiltonian_smul_of_isDiagonalRelativeCountMetricSlice`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DiagonalMetricModularBridge.spectral_dirac_sq_eq_countModularHamiltonian_of_isDiagonalRelativeCountMetricSlice`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/DiracMetricCompatibility.lean`

- **`InfoGeometry.Canonical.DiracMetricCompatibility.canonicalDiracOfMetric_isPositive`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/Drazin.lean`

- **`InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection_mul_projection`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Drazin.IsDrazinInverse.fitting_decomposition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Drazin.IsDrazinInverse.inverse_eq_pow_mul_pow`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Drazin.IsDrazinInverse.nilpotent_comm_self`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection_add_complementaryProjection`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection_comm`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection_mul_complementaryProjection`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/DrazinCoreFlow.lean`

- **`InfoGeometry.Canonical.CertifiedInverseKernel.A_pow_mul_nilpotentProj_eq_zero_of_index_le`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.nilpotentPart_pow_succ_eq_zero_of_index_le`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.Drazin.IsDrazinInverse.commute_projection`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Drazin.IsDrazinInverse.core_eq_projection_mul`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/DrazinDescriptorSystems.lean`

- **`InfoGeometry.Canonical.CertifiedInverseKernel.ambientFlow_eq_coreFlow_mul_nilpotentFlow`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.ambientFlow_eq_nilpotentFlow_mul_coreFlow`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.coreFlow_commute_nilpotentFlow`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.drazinDescriptorSystemsIsScalarTowerRealEndHEndH`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`, `rfl-like`
- **`InfoGeometry.Canonical.drazinDescriptorSystemsSMulCommClassRealEndHEndH`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`, `rfl-like`

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
- **`InfoGeometry.Canonical.DualConnections.e_m_connection_sum`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DualConnections.fisherBilinear_comm`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DualConnections.fisherBilinear_self_nonneg`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DualConnections.fisherMetric_of_finProb`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DualConnections.fisher_metric_eq_hessian_KL`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/DualConnectionsFiniteExpFamily.lean`

- **`InfoGeometry.Canonical.DualConnections.finiteExpFamilyAlphaConnection_deformation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DualConnections.finiteExpFamilyProbMap_apply_toReal`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DualConnections.fisherMetric_eq_covariance`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DualConnections.fisherQuadratic_eq_fisherBilinear_centeredScore`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/EPAndGroupInverse.lean`

- **`InfoGeometry.Canonical.CertifiedInverseKernel.isEP_iff_comm`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.isEP_iff_dilationGap_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.moorePenrose_isDrazinInverse_one_of_isEP`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.mpRangeProjector_eq_metricProjector_of_isEP`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.rightChiralAnomaly_eq_chiralAnomaly_of_isEP`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.rightProjectorMismatch_eq_projectorMismatch_of_isEP`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.spectralProjector_commutator_dilationGap_eq_zero_of_isEP`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.InverseKernel.isEP_iff_dilationGap_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.InverseKernel.mpRangeProjector_eq_metricProjector_of_isEP`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/EPDefectAlgebra.lean`

- **`InfoGeometry.Canonical.CertifiedInverseKernel.dilationGap_eq_half_smul_mpInverseCommutator`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.drazinCoreProj_idempotent`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.mpInverseCommutator_eq_zero_iff_isEP`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.mpLeftProj_idempotent`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.mpRightProj_idempotent`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.spectralProjector_commutator_dilationGap_eq_neg_half_chiralAnomaly_of_mpRightCommute`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.spectralProjector_commutator_dilationGap_eq_zero_of_mpRightCommute_of_chiralScale_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`

### `lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean`

- **`InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.bogoliubovConjugate_liftedEinsteinAnomalyOperator_eq_exp_mul_mul_exp_neg`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.bogoliubovConjugate_liftedLeftChiralAnomalyOperator_eq_exp_mul_mul_exp_neg`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.bogoliubovConjugate_liftedLeftChiralAnomalyOperator_ne_zero_iff_of_commute_generator`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.bogoliubovConjugate_liftedRightChiralAnomalyOperator_eq_exp_mul_mul_exp_neg`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.bogoliubovConjugate_liftedRightChiralAnomalyOperator_ne_zero_iff_of_commute_generator`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.deriv_bogoliubovConjugate_liftedEinsteinAnomalyOperator_at_zero_eq_zero_of_commute_generator`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.liftedChiralAnomalyOperator_apply_to_doubled`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.liftedEinsteinAnomalyOperator_apply_to_doubled`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.liftedEinsteinAnomalyOperator_ne_zero_iff`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.liftedEinsteinAnomalyOperator_relativeModularDeriv_eq_modularGaugeDeriv_of_commute_scalePart`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.liftedEinsteinAnomalyOperator_relativeModularDeriv_eq_modularGaugeDeriv_sub_relativeModularSinkDeriv`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.liftedEinsteinAnomalyOperator_relativeModularDeriv_eq_zero_of_commute_parts`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.liftedEinsteinAnomalyOperator_relativeModularSourceDeriv_add_relativeModularSinkDeriv`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.liftedRightChiralAnomalyOperator_apply_to_doubled`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.liftedRightChiralAnomalyOperator_ne_zero_iff`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.minusProjectorFlux_liftedEinsteinAnomalyOperator`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.plusProjectorFlux_liftedEinsteinAnomalyOperator`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.StarCertifiedConformalInference.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.StarCertifiedConformalInference.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.ConformalUnification.StarCertifiedConformalInference.liftedLeftChiralAnomalyOperator_star_eq_neg`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`

### `lean/InfoGeometry/Canonical/EmpiricalChecks.lean`

- **`InfoGeometry.Canonical.EmpiricalChecks.switch_selectedRoutingEpsilon_le_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.EmpiricalChecks.twoState_freeEnergy_identity_unit`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.EmpiricalChecks.twoState_gibbs_sum_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.EmpiricalChecks.twoState_partition_pos`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/Fock.lean`

- **`InfoGeometry.Canonical.Fock.bayesianUpdate_eq_creationExcitation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Fock.dataPart_eq_creation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Fock.modelPart_eq_annihilation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/FormalScaffold.lean`

- **`InfoGeometry.Canonical.Bregman.pythagorean_law`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

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

### `lean/InfoGeometry/Canonical/GeneralizedMetricCore.lean`

- **`InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed.decompose`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed.eta_comp_metric_eq_polarization`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed.eta_comp_minusProjector`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed.eta_comp_plusProjector`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed.metric_conjugates_eta`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed.metric_sq_eq_neg_id`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed.minusProjector_idempotent`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed.plusProjector_comp_minusProjector`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed.plusProjector_idempotent`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed.polarization_comp_minusProjector`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GeneralizedMetricCore.GeneralizedMetricSeed.polarization_comp_plusProjector`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GeneralizedMetricCore.tomitaGeneralizedMetricSeed_decompose`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GeneralizedMetricCore.tomitaGeneralizedMetricSeed_minusProjector_eq_self_of_mem_minusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GeneralizedMetricCore.tomitaGeneralizedMetricSeed_minusProjector_mem_minusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GeneralizedMetricCore.tomitaGeneralizedMetricSeed_plusProjector_eq_self_of_mem_plusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GeneralizedMetricCore.tomitaGeneralizedMetricSeed_plusProjector_mem_plusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/GeneralizedMetricPolarizedBridge.lean`

- **`InfoGeometry.Canonical.GeneralizedMetricPolarizedBridge.PolarizedRelativeModularPair.minus_lift_fixed_by_tomitaGeneralizedMetric`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GeneralizedMetricPolarizedBridge.PolarizedRelativeModularPair.plus_lift_fixed_by_tomitaGeneralizedMetric`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/GeneralizedMetricRecompositionBridge.lean`

- **`InfoGeometry.Canonical.GeneralizedMetricRecompositionBridge.PolarizedRecompositionData.generalizedMetricPotentialShadow_eq_zero_iff_exactPotentialRecomposition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GeneralizedMetricRecompositionBridge.PolarizedRecompositionData.generalizedMetricTwistShadow_eq_zero_iff_exactLogRecomposition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GeneralizedMetricRecompositionBridge.PolarizedRecompositionData.recomposedLogDensity_eq_commonCarrier_add_generalizedMetricTwistShadow`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GeneralizedMetricRecompositionBridge.PolarizedRecompositionData.recomposedModularPotential_eq_commonCarrier_add_generalizedMetricPotentialShadow`** — `V2/dead-public-theorem`
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
- **`InfoGeometry.Canonical.MoE.labelGenerator_sq_minus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.labelGenerator_sq_plus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.modeDiracAction_respects_grading`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.modewiseCliffordState_split`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.parity_minus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.parity_plus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.splitB11_splitBasis_orthogonal`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.splitQ11_splitBasisMinus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.splitQ11_splitBasisPlus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
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

- **`InfoGeometry.Canonical.GrandSynthesis.cl11_bottDirac_sq_eq_zero_of_lichnerowiczBalanced`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/GrandSynthesisGeometry.lean`

- **`InfoGeometry.Canonical.GrandSynthesis.logAbsDetMatrix_kronecker`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GrandSynthesis.logAbsDetMatrix_mul`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GrandSynthesis.logAbsJacDetCLM_comp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GrandSynthesis.log_spectralMongeAmpereDensity_eq_basepointLogVolume`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/GrandSynthesisSingular.lean`

- **`InfoGeometry.Canonical.GrandSynthesis.regularRadialTransportCloses_of_boundaryGenerator_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/GrandSynthesisThermo.lean`

- **`InfoGeometry.Canonical.GrandSynthesis.doublyStochastic_sinkhornEntropyMonotoneRN`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GrandSynthesis.ricci_component_constant_of_geometricEquilibrium`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GrandSynthesis.thermodynamicEquilibrium_of_doublyStochastic`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/GrandUnification.lean`

- **`InfoGeometry.Canonical.GrandUnification.JordanKKTData.detJ_pos`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GrandUnification.JordanKKTData.dual_potential_mixed_identity`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GrandUnification.JordanKKTData.generalized_pythagorean_theorem`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GrandUnification.JordanKKTData.mixed_bregman_identity`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GrandUnification.JordanKKTData.projection_minimizes`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.GrandUnification.JordanKKTData.projection_unique`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

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

- **`InfoGeometry.Canonical.IB.FrozenFiniteRegime.ofReal_toReal_fin_kl_div_cond`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.FrozenFiniteRegime.ofReal_toReal_fin_kl_div_encoder`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.baScoreFrozen_slice_toReal_pos`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/IBCanonical.lean`

- **`InfoGeometry.Canonical.IB.baStep_encoderMassNndist_le`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.baStep_eq_of_scoreRay_eq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.baStep_eq_scoreRay_gaugeSection`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.baStep_pointwise_massNndist_le`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.baStep_radial_projective_split`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.frozenFreeEnergy_eq_gap_minus_logPartition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.frozenVariational_descent`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/IBFiniteIteration.lean`

- **`InfoGeometry.Canonical.IB.ibTrajectory_step_descent_frozenTarget`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibTrajectory_step_gap_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibTrajectory_variational_descent_currentTarget`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/IBFiniteMonotonicity.lean`

- **`InfoGeometry.Canonical.IBFiniteMonotonicity.IB_monotone_descent_finite_fullSupport`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IBFiniteMonotonicity.encoderDescent_finite_fullSupport`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IBFiniteMonotonicity.finiteSliceJaynes_fullSupportPrior`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IBFiniteMonotonicity.finiteSliceObjective_eq_kl_to_next_minus_logPartition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IBFiniteMonotonicity.finiteSliceObjective_minimized_by_IBNextEncoder`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IBFiniteMonotonicity.ibDescentWitness_finite_fullSupport`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/IBFinitePythagorean.lean`

- **`InfoGeometry.Canonical.IBFinitePythagorean.finiteWeightedKL_bind_marginal_decomposition_fullSupport`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.IBFinitePythagorean.finiteWeightedKL_bind_marginal_decomposition`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.IBFinitePythagorean.ibMarginalDescentWitness_finite_fullSupport`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/IBFreeEnergy.lean`

- **`InfoGeometry.Canonical.IBFreeEnergy.klDivENN_self`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/IBFrozenDescent.lean`

- **`InfoGeometry.Canonical.IB.baFrozenTargetGap_eq_baFrozenTargetGapWith_induced`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStepFrozen_descent_frozenTargetGap`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibVariationalFunctionalLoose_eq_sum_local`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibVariationalFunctional_frozen_descent_of_gap_decomposition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibVariationalFunctional_le_loose`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/IBFrozenModularBridge.lean`

- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStepFrozen_scalarModularPotential_sub_logPartitionFrozen_eq_betaKL`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/IBFunctional.lean`

- **`InfoGeometry.Canonical.IBFunctional.IBMarginalize_congr`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IBFunctional.bindEncoderMeasure_univ`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/IBGaugeBridge.lean`

- **`InfoGeometry.Canonical.IBGaugeBridge.IBGibbsMeasure_shift_eq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
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
- **`InfoGeometry.Canonical.IBMeasure.IBPartitionFunction_eq_lintegral`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IBMeasure.rnDeriv_IBGibbs_eq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IBMeasure.rnDeriv_IBUnnormalized_eq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/IBMonotonicity.lean`

- **`InfoGeometry.Canonical.IBMonotonicity.IB_monotone_descent`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

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
- **`InfoGeometry.Canonical.IB.FullSupportScoreSlice.sameRay_toPositiveMeasure`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
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
- **`InfoGeometry.Canonical.IB.ScoreRay.normalize_projectiveState`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ScoreRay.normalize_toProjectiveState`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ScoreRay.projectiveState_mk`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.pmf_normalize_apply_toReal`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`, `rfl-like`
- **`InfoGeometry.Canonical.IB.pmf_normalize_eq_self`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.scoreProjectiveGauge_eq_of_sameScoreRay`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/IBPythagorean.lean`

- **`InfoGeometry.Canonical.IBPythagorean.IB_marginal_descent_of_pythagorean`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IBPythagorean.IB_marginal_descent_of_witness`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IBPythagorean.IB_next_marginal_descent_of_pythagorean`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IBPythagorean.IB_next_marginal_descent_of_witness`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IBPythagorean.encoderKernel_isMarkovKernel`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IBPythagorean.ibNextMarginalPythagoreanWitness_of_marginalization`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/IBTilted.lean`

- **`InfoGeometry.Canonical.IB.baFrozenTilted_apply_singleton`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
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
- **`InfoGeometry.Canonical.IB.ennreal_baScoreFrozenMeasure_mass`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ennreal_baScoreMeasure_mass`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/IBUpdate.lean`

- **`InfoGeometry.Canonical.IB.baNormalize_pointwise_massNndist_le_zero_of_sameScoreRay`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.baScore_eq_baScoreFrozen_induced`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.finProbMassNndist_eval_le_encoderMassNndist`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoProjectiveState_eq_of_sameScoreRay`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoProjectiveState_eq_of_scoreRay_eq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoProjectiveState_eq_of_score_ray_scale`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStepFrozen_eq_of_score_ray_scale`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStepFrozen_eq_prior_of_uniformDistortion`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStep_dilation_split`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStep_encoderMassNndist_le_of_massRecipLipschitz`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStep_encoderMassNndist_le_of_normalize_intrinsicNonzero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStep_encoderMassNndist_le_zero_of_sameScoreRay`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStep_encoderMassNndist_le_zero_of_scoreRay_eq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStep_encoderNndist_le_of_pointwise`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStep_eq_frozen_induced`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStep_eq_of_sameScoreRay`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStep_pointwise_massNndist_le_of_normalize_intrinsicNonzero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
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

- **`InfoGeometry.Canonical.InformationCalculus.ModularRadonNikodymData.deriv_informationPartitionFunction_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.InformationCalculus.ModularRadonNikodymData.hasDerivAt_informationPartitionFunction_zero_modularHamiltonian`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.InformationCalculus.ModularRadonNikodymData.informationPartitionFunction_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/InformationTorsion.lean`

- **`InfoGeometry.Canonical.InformationTorsion.FlatDualConnections.torsion_free_nabla`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.InformationTorsion.FlatDualConnections.torsion_free_nablaStar`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/InformationalLichnerowicz.lean`

- **`InfoGeometry.Canonical.InformationalLichnerowicz.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.InformationalLichnerowicz.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/InverseKernelAlgebra.lean`

- **`InfoGeometry.Canonical.CertifiedInverseKernel.metricComplementaryProjector_idempotent`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.metricComplementaryProjector_mul_metricProjector`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.metricComplementaryProjector_star`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.metricProjector_add_metricComplementaryProjector`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.metricProjector_mul_metricComplementaryProjector`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.mpRangeComplementaryProjector_idempotent`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.mpRangeComplementaryProjector_mul_mpRangeProjector`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.mpRangeComplementaryProjector_star`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.mpRangeProjector_add_mpRangeComplementaryProjector`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.mpRangeProjector_mul_mpRangeComplementaryProjector`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.projectorMismatch_sub_rightProjectorMismatch_eq_two_smul_dilationGap`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.rightChiralAnomaly_eq_rightProjectorMismatch_commutator_mpRange`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.rightProjectorMismatch_sub_projectorMismatch_eq_neg_two_smul_dilationGap`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.spectralComplementaryProjector_idempotent`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`

### `lean/InfoGeometry/Canonical/InverseKernelCartanCore.lean`

- **`InfoGeometry.Canonical.CertifiedInverseKernel.GammaS_eq_spectralProjector_sub_spectralComplementaryProjector`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.GammaS_eq_two_mul_spectralProjector_sub_one`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.GammaS_mul_spectralComplementaryProjector`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.GammaS_mul_spectralProjector`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.GammaS_sq_eq_one`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.isSpectralNonCompact_iff_anticommute_GammaS`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.spectralComplementaryProjector_commutes_spectralGradingFlow`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.spectralComplementaryProjector_fixed_under_spectralGradingFlow`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.spectralComplementaryProjector_isSpectralCompact`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.spectralGradingFlow_add`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.spectralGradingFlow_eq_cosh_add_sinh_GammaS`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.spectralGradingFlow_zero`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.spectralProjector_commutes_spectralGradingFlow`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.spectralProjector_fixed_under_spectralGradingFlow`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.spectralProjector_isSpectralCompact`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.thetaS_involutive`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.instIsScalarTowerRealContinuousLinearMapId_infoGeometry_1`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`, `rfl-like`
- **`InfoGeometry.Canonical.instSMulCommClassRealContinuousLinearMapId_infoGeometry_1`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`, `rfl-like`

### `lean/InfoGeometry/Canonical/InverseKernelNormalForm.lean`

- **`InfoGeometry.Canonical.CertifiedInverseKernel.chiralAnomaly_eq_zero_of_spectralMetricCommute`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.dilationGap_fixed_under_spectralGradingFlow_of_spectralMoorePenroseCommute`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.dilationGap_isSpectralCompact_of_spectralMoorePenroseCommute`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.metricProjector_fixed_under_spectralGradingFlow_of_spectralMetricCommute`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.metricProjector_isSpectralCompact_of_spectralMetricCommute`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.mpRangeProjector_fixed_under_spectralGradingFlow_of_spectralRangeCommute`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.mpRangeProjector_isSpectralCompact_of_spectralRangeCommute`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.projectorMismatch_fixed_under_spectralGradingFlow_of_spectralMetricCommute`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.projectorMismatch_isSpectralCompact_of_spectralMetricCommute`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.rightChiralAnomaly_eq_zero_of_spectralRangeCommute`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.spectralMetricCommute_of_chiralAnomaly_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.CertifiedInverseKernel.spectralRangeCommute_of_rightChiralAnomaly_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.InverseKernel.chiralAnomaly_eq_zero_of_spectralMetricCommute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.InverseKernel.rightChiralAnomaly_eq_zero_of_spectralRangeCommute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.InverseKernel.spectralMetricCommute_of_chiralAnomaly_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.InverseKernel.spectralRangeCommute_of_rightChiralAnomaly_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.instIsScalarTowerRealContinuousLinearMapId_infoGeometry_2`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`, `rfl-like`
- **`InfoGeometry.Canonical.instIsTopologicalRingContinuousLinearMapRealId_infoGeometry_2`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.instSMulCommClassRealContinuousLinearMapId_infoGeometry_2`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`, `rfl-like`

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

### `lean/InfoGeometry/Canonical/KKTCore.lean`

- **`InfoGeometry.Canonical.KKTCore.gNegOnePart_add`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KKTCore.gNegOnePart_mul_gNegOnePart_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KKTCore.gNegOnePart_smul`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KKTCore.gOnePart_add`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KKTCore.gOnePart_mul_gOnePart_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KKTCore.gOnePart_smul`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/KKTGeneralizedInverseBridge.lean`

- **`InfoGeometry.Canonical.KKTGeneralizedInverseBridge.mpInverseCommutator_isGZero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/KKTGeneralizedMetricBridge.lean`

- **`InfoGeometry.Canonical.KKTGeneralizedMetricBridge.canonical_gZeroPart_eq_generalizedMetric_blockDiagonal`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KKTGeneralizedMetricBridge.canonical_metric_comp_minusProjector`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KKTGeneralizedMetricBridge.canonical_metric_comp_plusProjector`** — `V2/dead-public-theorem`
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

- **`InfoGeometry.Canonical.KMSSinkhornBridge.exp_neg_jacobianLogPotential_eq_jacobianRelativeVolume`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KMSSinkhornBridge.ibRNPotential_eq_jacobianLogPotential_of_relativeVolume_match`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KMSSinkhornBridge.ibRNPotential_eq_scalarModularPotential_relativeVolumeChange`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KMSSinkhornBridge.jacobianLogPotential_eq_scalarModularPotential`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/KMSSinkhornSeedState.lean`

- **`InfoGeometry.Canonical.KMSSinkhornBridge.expectationSeedFunctional_id`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KMSSinkhornBridge.omegaSeed_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KMSSinkhornBridge.omegaSeed_nonzero_of_thermalVacuum`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/KMSSinkhornWeightedTransport.lean`

- **`InfoGeometry.Canonical.KMSSinkhornBridge.ibRNPotentialBarrierBudget_pos`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KMSSinkhornBridge.ibRNPotential_approxKMSClosure_of_ibDynamics_weighted`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KMSSinkhornBridge.ibRNPotential_approxKMSClosure_of_ibDynamics_weighted_from_jointKernel_commutator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

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
- **`InfoGeometry.Canonical.KreinDiracPolarizationBridge.transportEnd_id`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/KreinDiracSpectralLift.lean`

- **`InfoGeometry.Canonical.KreinDiracSpectralLift.kreinDiracSpectralLift_of_strictSymmetry`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KreinDiracSpectralLift.transportDiracFlow_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/KreinDiracWeightFunctionalLift.lean`

- **`InfoGeometry.Canonical.KreinDiracWeightFunctionalLift.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KreinDiracWeightFunctionalLift.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KreinDiracWeightFunctionalLift.transportDiracFlow_add_of_strictSymmetry`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KreinDiracWeightFunctionalLift.transportedThermalFlow_add_of_strictSymmetry`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/KreinDoubledAtom.lean`

- **`InfoGeometry.Canonical.KreinDoubledAtom.Atom.eps_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KreinDoubledAtom.Atom.j_eps_anticomm`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KreinDoubledAtom.Atom.j_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KreinDoubledAtom.Atom.k_eq_j_comp_eps`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KreinDoubledAtom.Atom.k_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KreinDoubledAtom.Core.eps_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KreinDoubledAtom.Core.j_eps_anticomm`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KreinDoubledAtom.Core.j_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KreinDoubledAtom.Core.k_eq_j_comp_eps`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KreinDoubledAtom.Core.k_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KreinDoubledAtom.Core.pi_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KreinDoubledAtom.J_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KreinDoubledAtom.K_sq_eq_neg_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KreinDoubledAtom.eps_comp_J`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KreinDoubledAtom.eps_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/KreinLadder.lean`

- **`InfoGeometry.Canonical.KreinLadder.InformationLadder.a_persistent`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/LLNCore.lean`

- **`InfoGeometry.Canonical.LLN.ae_tendsto_ratio_to_rnDeriv_holds`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`, `rfl-like`
- **`InfoGeometry.Canonical.LLN.fixed_partition_slln_holds`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/LogGenerator.lean`

- **`InfoGeometry.Canonical.DefectiveDescentLogGenerator.map_mul_defect`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OperatorLogGenerator.map_mul_of_commute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/LogSpineBridge.lean`

- **`InfoGeometry.Canonical.LogSpine.jordan_logdet_eq_zeta_determinant`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.LogSpine.kahler_spine_entropy_identity`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/LogSumExp.lean`

- **`InfoGeometry.Canonical.LogSumExp.logSumExp_eq_log_partition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/LorentzianRouting.lean`

- **`InfoGeometry.Canonical.Attention.timelike_dominance`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/MajoranaKitaevSpinorBridge.lean`

- **`InfoGeometry.Canonical.MajoranaKitaevSpinorBridge.MajoranaKitaevSpinorRegularizationPackage.drazinProjection_ne_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MajoranaKitaevSpinorBridge.MajoranaKitaevSpinorRegularizationPackage.hD`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MajoranaKitaevSpinorBridge.MajoranaKitaevSpinorRegularizationPackage.hMP`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MajoranaKitaevSpinorBridge.MajoranaKitaevSpinorRegularizationPackage.leftProjector_ne_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MajoranaKitaevSpinorBridge.MajoranaKitaevSpinorRegularizationPackage.rightProjector_ne_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MajoranaKitaevSpinorBridge.WeylBoundarySpinorPair.psiMinus_ne_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MajoranaKitaevSpinorBridge.WeylBoundarySpinorPair.psiMinus_weyl`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MajoranaKitaevSpinorBridge.WeylBoundarySpinorPair.psiMinus_zeroMode`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MajoranaKitaevSpinorBridge.WeylBoundarySpinorPair.psiPlus_ne_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MajoranaKitaevSpinorBridge.WeylBoundarySpinorPair.psiPlus_weyl`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MajoranaKitaevSpinorBridge.WeylBoundarySpinorPair.psiPlus_zeroMode`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MajoranaKitaevSpinorBridge.exists_nontrivial_regularization_pair_of_simplifiedBoundaryModel`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/MajoranaKreinCartanSplit.lean`

- **`InfoGeometry.Canonical.MajoranaKreinCartanSplit.comparisonGaugeGenerator_isPhaseLinear`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MajoranaKreinCartanSplit.comparisonReadout_phasePart_eq_zero_of_isPotentialKillingOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MajoranaKreinCartanSplit.comparisonSourceGenerator_isPhaseAntilinear`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MajoranaKreinCartanSplit.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MajoranaKreinCartanSplit.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MajoranaKreinCartanSplit.isPotentialKillingOperator_iff_comparisonReadoutStationary`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MajoranaKreinCartanSplit.projectiveDynamics_I_eq_projectiveMap_tomitaAtomSeed_phaseAxis`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MajoranaKreinCartanSplit.projectiveDynamics_J_eq_projectiveMap_tomitaAtomSeed_J`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MajoranaKreinCartanSplit.projectiveDynamics_epsilon_eq_projectiveMap_tomitaAtomSeed_eps`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MajoranaKreinCartanSplit.projectiveDynamics_tomitaAtomSeed_J_comp_eps`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.ProjectiveDynamics.J_comp_epsilon`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.MajoranaKreinCartanSplit.projectiveDynamics_tomitaAtomSeed_commute`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.ProjectiveDynamics.J_epsilon_commute`
  - Tags: `dead-candidate`, `wrapper-candidate`

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

### `lean/InfoGeometry/Canonical/ModularHessian.lean`

- **`InfoGeometry.Canonical.ModularHessian.fisherPart_eq_comparisonGeneratorMetric`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularHessian.fisher_metric_eq_symmetric_hessian`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularHessian.modularHessian_eq_comparisonGeneratorMetric`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularHessian.vortexPart_eq_comparisonGeneratorPhase`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ModularSpinorBridge.lean`

- **`InfoGeometry.Canonical.ModularSpinorBridge.MajoranaFrame.is_cl11`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularSpinorBridge.bayesian_update_as_spinor_bilinear`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularSpinorBridge.bayesian_update_as_spinor_bilinear_witness`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularSpinorBridge.fierzIdentity_true`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularSpinorBridge.modularFlowInducedTransport_eq_id_of_flow_id`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularSpinorBridge.modularSpinConnection_transport`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularSpinorBridge.transportedSplitVielbein_modularSpinConnection`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularSpinorBridge.weakValue_modularConjugate_eq_spinorBilinear_div_overlap`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularSpinorBridge.weakValue_numerator_eq_spinorBilinear`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ModularTwoStateCorrelation.lean`

- **`InfoGeometry.Canonical.ModularTwoStateCorrelation.channelCorrelationGap_eq_comparisonGeneratorMetric_sub_reference`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularTwoStateCorrelation.channelCorrelationGap_swap`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularTwoStateCorrelation.comparisonTransportCorrelation_eq_stateTransportCorrelation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularTwoStateCorrelation.comparisonTransportCorrelation_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularTwoStateCorrelation.comparisonTransportPhaseShiftedChannelCorrelation_eq_stateTransportPhaseShiftedChannelCorrelation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularTwoStateCorrelation.comparisonTransportPhaseShiftedChannelCorrelation_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularTwoStateCorrelation.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularTwoStateCorrelation.observableCorrelationGap_swap`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularTwoStateCorrelation.stateTransportCorrelation_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularTwoStateCorrelation.twoStateChannelCorrelation_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularTwoStateCorrelation.twoStateChannelCorrelation_self_eq_channelCorrelationAtState`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularTwoStateCorrelation.twoStateObservableCorrelation_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularTwoStateCorrelation.twoStateObservableCorrelation_swap`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ModularVolumeDeformationBridge.lean`

- **`InfoGeometry.Canonical.ModularVolumeDeformationBridge.projective_logVolumeDeformation_eq_raw_add_massShift`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularVolumeDeformationBridge.projective_logVolumeDeformation_eq_raw_sub_log_countRelativeVolumeChange`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularVolumeDeformationBridge.projective_modularPotential_eq_raw_sub_scalarModularPotential_relativeVolumeChange`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularVolumeDeformationBridge.projective_relativeVolumeDeformation_eq_massRatio_mul_raw`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularVolumeDeformationBridge.scalar_modularPotential_is_neg_log`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.RelativePotentialScalarBridge.scalarModularPotential_eq_neg_log`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/MongeAmpereCramerRao.lean`

- **`InfoGeometry.Canonical.MongeAmpereCramerRao.abs_squeezingLogShear_le_of_sinkhornTrajectory`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereCramerRao.squeezingEigen_product_eq_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/MongeAmpereDualSheetBridge.lean`

- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.dualSheetMongeAmpereConsistentAtBasepoint`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.minusBlockMap_rnEntropyDualSheetSourceOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.minusBlockMap_squeezingTransport`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.minusPointL_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.minusProjectorFlux_rnEntropyDualSheetSourceOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.minusProjectorFlux_squeezingTransport`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.minusToPlusBlockMap_rnEntropyDualSheetSourceOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.minusToPlusBlockMap_squeezingTransport`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.mongeAmpereDensityOperator_eq_exp_metricLogDet_smul_id`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.mongeAmpereDensityOperator_eq_exp_neg_kahlerPotentialRN_smul_id_of_rnEntropySource`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.mongeAmpereDensityOperator_eq_exp_smul_id_of_satisfiesMongeAmperePotential`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.mongeAmpereDensityOperator_eq_id_of_incompressible`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.mongeAmpereDensityOperator_eq_rnEntropyDualSheetSourceOp_of_rnEntropySource`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.plusBlockMap_rnEntropyDualSheetSourceOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.plusBlockMap_squeezingTransport`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.plusPointL_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.plusProjectorFlux_rnEntropyDualSheetSourceOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.plusProjectorFlux_squeezingTransport`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.plusToMinusBlockMap_rnEntropyDualSheetSourceOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MongeAmpereDualSheetBridge.plusToMinusBlockMap_squeezingTransport`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/MoorePenrose.lean`

- **`InfoGeometry.Canonical.MoorePenrose.chiralAnomaly_eq_zero_of_projectorMismatch_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

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

### `lean/InfoGeometry/Canonical/NoetherInference.lean`

- **`InfoGeometry.Canonical.NoetherInference.BayesianSymmetryOrbit.preserves_hessian`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.NoetherInference.BayesianSymmetryOrbit.update_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.NoetherInference.BayesianSymmetryOrbit.update_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.NoetherInference.InformationKillingField.preserves_hessian`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.NoetherInference.evalAt_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.NoetherInference.fisher_metric_eq_killing_form_of_orbit_base_relation_of_commutes_with_involution`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/OnsagerCasimirJ.lean`

- **`InfoGeometry.Canonical.OnsagerCasimirJ.JConjugate_involutive`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OnsagerCasimirJ.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OnsagerCasimirJ.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OnsagerCasimirJ.jPairedGeneratorCorrelation_metric`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OnsagerCasimirJ.jPairedGeneratorCorrelation_phase`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OnsagerCasimirJ.twoStateChannelCorrelation_J_reflect_eq_of_IsJInvariant`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/OnsagerReciprocity.lean`

- **`InfoGeometry.Canonical.OnsagerReciprocity.channelCorrelationAtState_swap`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OnsagerReciprocity.comparisonGeneratorMetric_swap`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OnsagerReciprocity.curvatureCoefficient_eq_probe_bracketDerivation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OnsagerReciprocity.curvatureCoefficient_swap_neg`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OnsagerReciprocity.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OnsagerReciprocity.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OnsagerReciprocity.operatorCurvatureHessianForm_diag`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OnsagerReciprocity.operatorMetricHessianForm_diag`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OnsagerReciprocity.operatorPhaseHessianForm_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OnsagerReciprocity.operatorPhaseHessianForm_eq_metric_comp_channelPhaseAxis`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OnsagerReciprocity.operatorSecondVariationForm_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OnsagerReciprocity.responseCoefficient_swap`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OnsagerReciprocity.toRelationalInformationDatum_bohmMadelung_stationary_iff_isPotentialKillingOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OnsagerReciprocity.toRelationalInformationDatum_comparisonGaugeGenerator_eq_phaseLinearPart`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OnsagerReciprocity.toRelationalInformationDatum_comparisonMetricPhaseReadout_pair_eq_bohmMadelung_constantStateGeneratorField_pair`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OnsagerReciprocity.toRelationalInformationDatum_comparisonMetricPhaseReadout_pair_eq_phaseLinearAntilinear_operator_pair`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OnsagerReciprocity.toRelationalInformationDatum_comparisonSourceGenerator_eq_phaseAntilinearPart`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OnsagerReciprocity.toRelationalInformationDatum_comparisonTransportGenerator_eq_gauge_add_source`** — `V2/dead-public-theorem`
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

- **`InfoGeometry.Canonical.OperatorAlgebraBridge.kk_supercomm_compact_of_even_rep`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/OperatorAlgebraModularAtom.lean`

- **`InfoGeometry.Canonical.OperatorAlgebraBridge.modular_atom_is_cl11`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/OperatorialCramerRao.lean`

- **`InfoGeometry.Canonical.OperatorialCramerRao.comparisonStateGeneratorMetric_self_nonneg`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OperatorialCramerRao.toRelationalInformationDatum_inv_comparisonGeneratorMetric_self_le_of_unit_response`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/OperatorialInformationLift.lean`

- **`InfoGeometry.Canonical.OperatorialInformationLift.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OperatorialInformationLift.instCompleteSpaceEndH`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
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

### `lean/InfoGeometry/Canonical/OperatorialUncertainty.lean`

- **`InfoGeometry.Canonical.OperatorialUncertainty.phaseShiftedTwoStateChannelCorrelation_self_sq_le_of_IsPhaseLinear`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OperatorialUncertainty.symmetricTwoStateChannelCorrelation_sq_add_phaseShifted_sq_le_of_IsPhaseLinear`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OperatorialUncertainty.toRelationalInformationDatum_comparisonGeneratorMetric_sq_add_phase_sq_le_of_IsPhaseLinear`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OperatorialUncertainty.toRelationalInformationDatum_comparisonGeneratorPhase_sq_le_of_IsPhaseLinear`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.OperatorialUncertainty.toRelationalInformationDatum_inv_comparisonGeneratorMetric_self_le_of_unit_phase_response_of_IsPhaseLinear`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/PartitionHierarchy.lean`

- **`InfoGeometry.Canonical.PartitionHierarchy.effectivePotential_eq_neg_inv_temp_mul_log_fiberPartition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PartitionHierarchy.grandCanonical_freeEnergy_eq_trivialEffectivePotential`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PartitionHierarchy.grandCanonical_potentialGC_eq_trivialLogPartitionPotential`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PartitionHierarchy.totalPartition_eq_sum_fiberPartition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/PerelmanWCore.lean`

- **`InfoGeometry.Canonical.PerelmanW.WFunctional_monotone_of_nonneg_dissipation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/PerelmanWSpinorial.lean`

- **`InfoGeometry.Canonical.PerelmanW.deriv_W_eq_abs_spinorial_of_normalized_tracking`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/PhaseSpaceCausalFlowBridge.lean`

- **`InfoGeometry.Canonical.PhaseSpaceCausalFlowBridge.LeafOutputs.chiralGrading_isGZero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceCausalFlowBridge.TrunkOutputs.CIK_AD_isGNegOne`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceCausalFlowBridge.TrunkOutputs.CIK_AMP_isGNegOne`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceCausalFlowBridge.TrunkOutputs.CIK_A_isGOne`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceCausalFlowBridge.TrunkOutputs.chiralGrading_isGZero'`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceCausalFlowBridge.TrunkOutputs.dilationGap_isGZero'`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceCausalFlowBridge.TrunkOutputs.drazinCoreProj_isGZero'`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceCausalFlowBridge.TrunkOutputs.mpChiralGap_isGZero'`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceCausalFlowBridge.TrunkOutputs.toLeafOutputs`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceCausalFlowBridge.correctedOwner_trunk_outputs`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceCausalFlowBridge.correctedOwner_trunk_outputs_struct`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceCausalFlowBridge.phaseTransport_descends_to_generalizedMetricTwistShadow`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceCausalFlowBridge.toDoubledCopyRho_comp_phaseRotation_eq_KKT_dilationOperator`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.PhaseSpaceConformalKKTBridge.toDoubledCopyRho_comp_phaseRotation_eq_KKT_dilationOperator`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/PhaseSpaceConformalKKTBridge.lean`

- **`InfoGeometry.Canonical.PhaseSpaceConformalKKTBridge.CertifiedConformalInference.D_isGZero`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceConformalKKTBridge.CertifiedConformalInference.drazinCoreProj_isGZero`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceConformalKKTBridge.CertifiedConformalInference.mpChiralGap_isGZero`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceConformalKKTBridge.toDoubledCopyRho_comp_phaseMinusProjector_eq_KKT_minusProjector`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.KKTGeneralizedMetricBridge.toDoubledCopyRho_comp_phaseMinusProjector_eq_canonical_minusProjector`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceConformalKKTBridge.toDoubledCopyRho_comp_phasePlusProjector_eq_KKT_plusProjector`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.KKTGeneralizedMetricBridge.toDoubledCopyRho_comp_phasePlusProjector_eq_canonical_plusProjector`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceConformalKKTBridge.toDoubledCopyRho_comp_phaseRotation_eq_KKT_dilationOperator`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.KKTGeneralizedMetricBridge.toDoubledCopyRho_comp_phaseRotation_eq_dilationOperator`
  - Tags: `proof-infrastructure`, `wrapper-candidate`

### `lean/InfoGeometry/Canonical/PhaseSpaceGeneralizedMetricChiralityBridge.lean`

- **`InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge.fromDoubledCopyRho_toDoubledCopyRho`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge.ofMetric_generalizedMetricForm_eq_doubledInner`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge.ofMetric_minusProjector_realized_is_chiralityMinus_fixed`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge.ofMetric_plusProjector_realized_is_chiralityPlus_fixed`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge.realizedPolarization_eq_b_conj_modular_j`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge.toDoubledCopyRho_comp_bTransformInv_eq_realized`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge.toDoubledCopyRho_comp_bTransform_eq_realized`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge.toDoubledCopyRho_comp_ofMetric_polarization_eq_chiralityDifference`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge.toDoubledCopyRho_fromDoubledCopyRho`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/PhaseSpacePolarizedBridge.lean`

- **`InfoGeometry.Canonical.PhaseSpacePolarizedBridge.MinusRestrictedRelativeModularData.realize_phaseLift_fixed_by_realizedMinusProjector`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpacePolarizedBridge.PlusRestrictedRelativeModularData.realize_phaseLift_fixed_by_realizedPlusProjector`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpacePolarizedBridge.PolarizedRelativeModularPair.minus_phaseLift_fixed_by_phaseMinusProjector`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpacePolarizedBridge.PolarizedRelativeModularPair.plus_phaseLift_fixed_by_phasePlusProjector`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/PhaseSpaceRecompositionBridge.lean`

- **`InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.minusPhaseTransportLift_realize_fixed_by_realizedPlusProjector`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.minusPhaseTransportLift_realizes_to_plusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.plusPhaseTransportLift_realize_fixed_by_realizedMinusProjector`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceRecompositionBridge.PolarizedRecompositionData.plusPhaseTransportLift_realizes_to_minusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/PhaseSpaceRecompositionExample.lean`

- **`InfoGeometry.Canonical.PhaseSpaceRecompositionExample.ambient_projectiveLogDensity_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceRecompositionExample.ambient_projectiveLogDensity_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceRecompositionExample.exactLogRecomposition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceRecompositionExample.exactPotentialRecomposition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceRecompositionExample.generalizedMetricPotentialShadow_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceRecompositionExample.generalizedMetricTwistShadow_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceRecompositionExample.localRay_logDensity_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceRecompositionExample.minusPhaseTransportLift_realizes_fixed_by_tomita_plusProjector`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceRecompositionExample.minusPhaseTransportLift_realizes_through_doubled_corridor`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceRecompositionExample.plusPhaseTransportLift_realizes_fixed_by_tomita_minusProjector`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceRecompositionExample.plusPhaseTransportLift_realizes_through_doubled_corridor`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceRecompositionExample.sourceRay_logDensity_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceRecompositionExample.sourceRay_logDensity_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceRecompositionExample.targetRay_logDensity_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceRecompositionExample.targetRay_logDensity_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/PhaseSpaceWeylCausalBridge.lean`

- **`InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge.SourceSpineAndWeylEndpoint.obstruction_diagonal_blocks`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge.SourceSpineAndWeylEndpoint.obstruction_minusProjector_mul_mul_plusProjector_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge.SourceSpineAndWeylEndpoint.obstruction_plusProjector_mul_mul_minusProjector_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge.WeylLeafOutputs.holonomy_eq_chiralScale_compat`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge.finiteDimensional_end_to_end_witness_of_projectorAgreementCertified_metricProjector_commute`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge.finiteDimensional_end_to_end_witness_of_projectorAgreement_metricProjector_commute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge.holonomy_eq_chiralScale_of_flat_from_conformal_compat_thin`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge.holonomy_eq_projectorObstruction_nnnorm_and_bogoliubovConjugate_liftedEinsteinAnomalyOperator_eq_self_of_flat_of_commute_generator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge.holonomy_eq_projectorObstruction_nnnorm_and_bogoliubovConjugate_liftedEinsteinAnomalyOperator_ne_zero_iff_of_flat_of_commute_generator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge.holonomy_eq_projectorObstruction_nnnorm_and_deriv_bogoliubovConjugate_liftedEinsteinAnomalyOperator_at_zero_eq_relativeModularSourceDeriv_of_flat_of_commute_gaugePart`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge.holonomy_eq_projectorObstruction_norm_of_flat_from_conformal`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge.holonomy_ne_zero_and_bogoliubovConjugate_liftedEinsteinAnomalyOperator_ne_zero_of_flat_of_noncommute_of_projectorAgreementCertified_of_commute_generator`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge.leaf_projectorObstruction_diagonal_blocks_and_holonomy_eq_projectorObstruction_nnnorm_of_flat`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge.leaf_projectorObstruction_offDiagonal_vanish_and_holonomy_eq_projectorObstruction_nnnorm_of_flat`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge.projectorAgreementCertified_metricProjector_commute_dilation_driver_and_holonomy_eq_projectorObstruction_nnnorm_of_flat_from_conformal`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge.projectorAgreement_metricProjector_commute_dilation_driver_and_holonomy_eq_projectorObstruction_nnnorm_of_flat_from_conformal`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge.toDoubledCopyRho_comp_phaseRotation_eq_KKT_dilationOperator`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.PhaseSpaceConformalKKTBridge.toDoubledCopyRho_comp_phaseRotation_eq_KKT_dilationOperator`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge.trunk_projectorObstruction_diagonal_blocks_and_holonomy_eq_projectorObstruction_nnnorm_of_flat`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge.trunk_projectorObstruction_offDiagonal_vanish_and_holonomy_eq_projectorObstruction_nnnorm_of_flat`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/PolarizedMadelungBridge.lean`

- **`InfoGeometry.Canonical.PolarizedMadelungBridge.PolarizedDoubledAmplitude.kreinExpectation_smul_id_of_mem_minusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PolarizedMadelungBridge.PolarizedDoubledAmplitude.kreinExpectation_smul_id_of_mem_plusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PolarizedMadelungBridge.PolarizedDoubledAmplitude.phaseOrbit_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PolarizedMadelungBridge.PolarizedDoubledAmplitude.sheet_decomposition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PolarizedMadelungBridge.PolarizedDoubledAmplitude.ψminus_mem_minusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PolarizedMadelungBridge.PolarizedDoubledAmplitude.ψplus_mem_plusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PolarizedMadelungBridge.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PolarizedMadelungBridge.kreinExpectation_minusPoint`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PolarizedMadelungBridge.kreinExpectation_plusPoint`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/PositiveRayCore.lean`

- **`InfoGeometry.Canonical.PositiveRayCore.Z_gaugeSection`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PositiveRayCore.gaugeSection_eq_exp_neg_modularPotential`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PositiveRayCore.logDensity_eq_neg_modularPotential`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PositiveRayCore.modularPotential_eq_neg_logDensity`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PositiveRayCore.ofConeInteriorStateSpace_toConeInteriorStateSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PositiveRayCore.toConeInteriorStateSpace_ofConeInteriorStateSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/QuantumGeometryDualSheetBridge.lean`

- **`InfoGeometry.Canonical.QuantumGeometryDualSheetBridge.dualSheetLift_cramerRaoMetricOp_eq_dualSheetLift_quantumGeometryOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.QuantumGeometryDualSheetBridge.dualSheetMetricOp_eq_dualSheetLift_cramerRaoMetricOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.QuantumGeometryDualSheetBridge.dualSheetMetricOp_eq_dualSheetLift_quantumGeometryOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.QuantumGeometryDualSheetBridge.minusBlockMap_dualSheetLift_quantumGeometryOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.QuantumGeometryDualSheetBridge.minusProjectorFlux_dualSheetLift_quantumGeometryOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.QuantumGeometryDualSheetBridge.minusToPlusBlockMap_dualSheetLift_quantumGeometryOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.QuantumGeometryDualSheetBridge.plusBlockMap_dualSheetLift_quantumGeometryOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.QuantumGeometryDualSheetBridge.plusProjectorFlux_dualSheetLift_quantumGeometryOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.QuantumGeometryDualSheetBridge.plusToMinusBlockMap_dualSheetLift_quantumGeometryOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/QuantumInference.lean`

- **`InfoGeometry.Canonical.QuantumInference.CCR.comm_a_a`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.QuantumInference.CCR.comm_a_adag`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.QuantumInference.CCR.comm_adag_adag`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/QuantumLieAlgebroidRosetta.lean`

- **`InfoGeometry.Canonical.QuantumLieAlgebroidRosetta.paper_anchor_eq_comparisonInducedDynamics`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.QuantumLieAlgebroidRosetta.paper_anchor_split_eq_gauge_add_source`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.QuantumLieAlgebroidRosetta.paper_channelPhaseAxis_apply_eq_comp_internalPhaseAxis`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.QuantumLieAlgebroidRosetta.paper_complexUnit_eq_internalPhaseAxis`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.QuantumLieAlgebroidRosetta.paper_generatorPhase_eq_metric_comp_internalPhaseAxis`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.QuantumLieAlgebroidRosetta.paper_inducedDatum_anchor_eq_stateInducedDynamics`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.QuantumLieAlgebroidRosetta.paper_metricPhase_pair_eq_metricBerry_of_anchor`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.QuantumLieAlgebroidRosetta.paper_phaseReadout_eq_metric_comp_internalPhaseAxis`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.QuantumLieAlgebroidRosetta.paper_schrodingerCurrent_eq_probe_anchor`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/QuasilatticeDirac.lean`

- **`InfoGeometry.Canonical.QuasilatticeDirac.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
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
- **`InfoGeometry.Canonical.RGFlow.exists_isStationaryAtScale_constantFlow`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RGFlow.generatedDiscreteFlow_succ`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RGFlow.generatedDiscreteFlow_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RGFlow.modularCliffordFlowInvariant_constantFlow_id`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RGFlow.tendsto_generatedDiscreteFlow_fixedPoint_of_contracting`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RealBdG.lean`

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
- **`InfoGeometry.Canonical.RealBdG.modularK_apply_modularK`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RealBdG.modularK_def`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RealBdG.modularK_eq_modularComplexI`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RealBdGSheetBridge.lean`

- **`InfoGeometry.Canonical.RealBdGSheetBridge.KAntilinearPart_liftedOperator_eq_zero_of_isGaugeBalanced`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RealBdGSheetBridge.KLinearPart_liftedOperator_eq_liftedOperator_of_isGaugeBalanced`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RealBdGSheetBridge.chiralImbalanceLift_is_KAntilinear`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RealBdGSheetBridge.commonModeLift_is_KLinear`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RealBdGSheetBridge.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
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

### `lean/InfoGeometry/Canonical/RelationalInformationCore.lean`

- **`InfoGeometry.Canonical.RelationalInformationCore.channelPhaseAxis_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelationalInformationCore.comparisonGeneratorPhase_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelationalInformationCore.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelationalInformationCore.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RelationalInformationDynamics.lean`

- **`InfoGeometry.Canonical.RelationalInformationDynamics.channelMetricAtState_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelationalInformationDynamics.constructiveRelationalDatum_comparisonFunctionalValue`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelationalInformationDynamics.constructiveRelationalDatum_comparisonGeneratorMetric_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelationalInformationDynamics.constructiveRelationalDatum_comparisonGeneratorPhase_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelationalInformationDynamics.constructiveRelationalDatum_firstVariation_comparison`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelationalInformationDynamics.constructiveRelationalDatum_informationFunctional`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelationalInformationDynamics.constructiveRelationalDatum_referenceFunctionalValue`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelationalInformationDynamics.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelationalInformationDynamics.observableLieHessian_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationFirstVariationMap_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationMixedSecondVariationMap_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationPhaseReadout_eq_metric_comp_modularComplexI`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelationalInformationDynamics.operatorMassieuExpectation_transport_intertwines_firstVariation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelationalInformationDynamics.operatorMassieuExpectation_transport_intertwines_hessian`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RelativeModularCore.lean`

- **`InfoGeometry.Canonical.RelativeModularCore.RelativeStatePair.compose_logDensity`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularCore.RelativeStatePair.compose_modularPotential`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularCore.RelativeStatePair.modularPotential_eq_logDensity_target_sub_source`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RelativeModularOperator.lean`

- **`InfoGeometry.Canonical.RelativeModularOperator.relativeModularOperator_diag_eq_exp_relativeLogDensity`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularOperator.relativeModularVolumeShadow_cocycle`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RelativeModularPolarizedBridge.lean`

- **`InfoGeometry.Canonical.RelativeModularPolarizedBridge.MinusRestrictedRelativeModularData.lift_eq_minusPoint_snd`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularPolarizedBridge.MinusRestrictedRelativeModularData.local_logDensity_eq_pullback_of_equal_shift`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularPolarizedBridge.MinusRestrictedRelativeModularData.local_modularPotential_eq_pullback_of_equal_shift`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularPolarizedBridge.MinusRestrictedRelativeModularData.local_projectiveLogGenerator_eq_pullback_ambient_add_shift`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularPolarizedBridge.PlusRestrictedRelativeModularData.lift_eq_plusPoint_fst`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularPolarizedBridge.PlusRestrictedRelativeModularData.local_logDensity_eq_pullback_of_equal_shift`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularPolarizedBridge.PlusRestrictedRelativeModularData.local_modularPotential_eq_pullback_of_equal_shift`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularPolarizedBridge.PlusRestrictedRelativeModularData.local_projectiveLogGenerator_eq_pullback_ambient_add_shift`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RelativeModularPotential.lean`

- **`InfoGeometry.Canonical.RelativeModularPotential.channelCorrelationAtState_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularPotential.comparisonMetricReadout_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularPotential.comparisonPhaseReadout_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorPhase_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularPotential.generator_eq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularPotential.modularSeed_eq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularPotential.toRelationalInformationDatum_comparisonGeneratorPhase_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularPotential.toRelationalInformationDatum_firstVariation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularPotential.toRelationalInformationDatum_informationFunctional`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularPotential.transportGenerator_eq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularPotential.value_eq_probe_generator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean`

- **`InfoGeometry.Canonical.RelativeModularProjectiveBridge.RestrictedRelativeModularData.local_projectiveLogGenerator_eq_pullback_ambient_add_shift`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularProjectiveBridge.RestrictedRelativeModularData.local_projectiveLogGenerator_eq_pullback_ambient_add_shift_ae`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularProjectiveBridge.RestrictedRelativeModularData.projectiveCountHamiltonianProfile_eq_pullback_ambient_add_shift`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RelativeModularRecomposition.lean`

- **`InfoGeometry.Canonical.RelativeModularRecomposition.PolarizedRecompositionData.carrier_eq_minus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularRecomposition.PolarizedRecompositionData.carrier_eq_plus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularRecomposition.PolarizedRecompositionData.exactLogRecomposition_iff_exactPotentialRecomposition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularRecomposition.PolarizedRecompositionData.exactLogRecomposition_of_sectorwiseExact`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularRecomposition.PolarizedRecompositionData.exactPotentialRecomposition_of_sectorwiseExact`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularRecomposition.PolarizedRecompositionData.recomposedLogDensity_eq_commonCarrier_of_sectorwiseExact`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularRecomposition.PolarizedRecompositionData.recomposedModularPotential_eq_commonCarrier_of_sectorwiseExact`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularRecomposition.PolarizedRecompositionData.recomposedModularPotential_eq_neg_recomposedLogDensity`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RelativeModularSingularization.lean`

- **`InfoGeometry.Canonical.RelativeModularSingularization.drazinProjection_ne_one_of_not_mem`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularSingularization.drazinProjection_ne_zero_of_mem`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularSingularization.isDrazinInverse_singularRelativeModularOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularSingularization.isMoorePenroseInverse_singularRelativeModularOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularSingularization.moorePenroseLeftProjector_ne_one_of_not_mem`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularSingularization.moorePenroseLeftProjector_ne_zero_of_mem`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularSingularization.moorePenroseRightProjector_ne_one_of_not_mem`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularSingularization.moorePenroseRightProjector_ne_zero_of_mem`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularSingularization.relativeModularPseudoBerezinianPotential_univ`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularSingularization.relativeModularPseudoBerezinianShadow_pos`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularSingularization.relativeModularPseudoVolumePotential_univ`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularSingularization.relativeModularPseudoVolumeShadow_self`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularSingularization.singularRelativeModularOperator_diag`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularSingularization.singularRelativeModularOperator_eq_relativeModularOperator_mul_supportProjector`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularSingularization.singularRelativeModularOperator_eq_supportProjector_mul_relativeModularOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularSingularization.singularRelativeModularOperator_offdiag`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularSingularization.singularRelativeModularPseudoInverse_diag`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularSingularization.singularRelativeModularPseudoInverse_eq_relativeModularOperator_mul_supportProjector`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularSingularization.singularRelativeModularPseudoInverse_eq_supportProjector_mul_relativeModularOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularSingularization.singularRelativeModularPseudoInverse_mul_supportProjector`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularSingularization.singularRelativeModularPseudoInverse_offdiag`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularSingularization.supportProjector_diag`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularSingularization.supportProjector_idempotent`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularSingularization.supportProjector_offdiag`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RelativePotentialCore.lean`

- **`InfoGeometry.Canonical.RelativePotentialCore.gaugeSection_eq_relativeDensity_mul_gaugeSection`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCore.representativeModularPotential_scale_left`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCore.representativeModularPotential_scale_right`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCore.representativeRelativeDensity_scale_left`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCore.representativeRelativeDensity_scale_right`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCore.representativeRelativeLogDensity_scale_scale`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean`

- **`InfoGeometry.Canonical.RelativePotentialCountBridge.averagedProjectiveCountHamiltonian_eq_averagedRawCountHamiltonian_sub_massShift`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.averagedProjectiveCountKreinTomitaTakesakiOp_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.averagedRawCountKreinTomitaTakesakiOp_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.averagedRawCountTomitaTakesakiOp_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.countMassShift_self`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.countMassShift_symm`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.exp_neg_countMassShift_eq_countRelativeVolumeChange`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.gaugeSectionFinProb_countRay_apply_toReal`** — `V2/dead-public-theorem`
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
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.projectiveLogGenerator_countRay_eq_projectiveCountHamiltonianProfile`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.rawCountDelta_cocycle`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.relativeCountDensity_eq_exp_neg_relativeCountModularProfile`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.relativeCountLogDensity_cocycle`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.relativeKreinTomitaTakesakiOp_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.relativeTomitaTakesakiOp_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.representativeModularPotential_positiveMeasureOfCounts_eq_relativeCountModularProfile`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.representativeRelativeDensity_positiveMeasureOfCounts_eq_relativeCountDensity`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialCountBridge.representativeRelativeLogDensity_positiveMeasureOfCounts_eq_relativeCountLogDensity`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RelativePotentialDiscreteBridge.lean`

- **`InfoGeometry.Canonical.RelativePotentialDiscreteBridge.normalize_toProjectiveState`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RelativePotentialScalarBridge.lean`

- **`InfoGeometry.Canonical.RelativePotentialScalarBridge.scalarLogDensity_eq_log`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialScalarBridge.scalarModularPotential_weylRescale_eq_sub_log`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativePotentialScalarBridge.scalarPositiveMeasure_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean`

- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.densityMatrixOfFinProb_diag`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.densityMatrixOfFinProb_offdiag`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.diagonalAverage_relativeModularPotentialOperator_eq_inv_card_mul_relativeModularVolumePotential`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.diagonalAverage_relativeModularPotentialOperator_eq_modularHamiltonianReadout`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.diagonalExpectation_firstQuantize`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.entropy_eq_diagonalExpectation_surprisalOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.firstQuantize_smul`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.hasDerivAt_informationPartitionFunction_zero_relativeTomitaTakesakiOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.hasDerivAt_logInformationPartitionFunction_zero_relativeCountLift_of_normalized`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.instCompleteSpaceEndHRouterAmplitude`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.instIsTopologicalRingEndHRouterAmplitude`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.logDensityOperator_diag`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.relativeCountModularPotentialOperator_cocycle`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.relativeKreinTomitaTakesakiOp_eq_diagonalAverage_rawLift_smul_eps`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.relativeKreinTomitaTakesakiOp_eq_modularHamiltonianReadout_relativeModularOperator_countRay_add_countMassShift_smul_eps`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.relativeLogDensityOperator_diag_eq_log_relativeModularOperator_diag`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.relativeLogDensityOperator_eq_firstQuantize_log_relativeModularOperator_diag`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.relativeLogDensityOperator_eq_logDensityOperator_sub`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.relativeModularHamiltonian_sub_countMassShift_cocycle`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.relativeModularHamiltonian_sub_countMassShift_eq_modularHamiltonianReadout_relativeModularOperator_countRay`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.relativeModularOperator_eq_firstQuantize_relativeDensity`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.relativeModularPotentialOperator_diag_eq_neg_log_relativeModularOperator_diag`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.relativeModularPotentialOperator_eq_logDensity_base_sub`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.relativeTomitaTakesakiOp_eq_modularHamiltonianReadout_relativeModularOperator_countRay_add_countMassShift_smul_id`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeSurprisalOperatorLift.surprisalOperator_diag`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RestrictedSheetContinuous.lean`

- **`InfoGeometry.Canonical.RestrictedSheetContinuous.GaugeBalancedEquiv.isGaugeBalanced`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.GaugeBalancedEquiv.minusProjectorFlux_liftedOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.GaugeBalancedEquiv.plusProjectorFlux_liftedOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.RestrictedSheetContinuousEquiv.ext_iff`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.RestrictedSheetContinuousEquiv.minusBlockMap_liftedOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
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
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.ShaleStinespringEquiv.liftedOperator_mul`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.ShaleStinespringEquiv.minusProjectorFlux_liftedOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedSheetContinuous.ShaleStinespringEquiv.plusProjectorFlux_liftedOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
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
- **`InfoGeometry.Canonical.RestrictedVolumeCharacter.dualSheetDiagonalScalarOp_one_neg_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedVolumeCharacter.dualSheetDiagonalScalarOp_one_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedVolumeCharacter.minusBlockMap_dualSheetDiagonalScalarOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedVolumeCharacter.minusProjectorFlux_dualSheetDiagonalScalarOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedVolumeCharacter.minusToPlusBlockMap_dualSheetDiagonalScalarOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedVolumeCharacter.plusBlockMap_dualSheetDiagonalScalarOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RestrictedVolumeCharacter.plusProjectorFlux_dualSheetDiagonalScalarOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
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
- **`InfoGeometry.Canonical.RicciMongeAmpere.einsteinTensor_transport_split_mixed_eq_zero_of_scalar_closure`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.isEinsteinKaehlerAtWith_to_exists`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.kaehlerRicciEvolution_beta_eq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.metricLogDet_differentiable`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.metricLogDet_fderiv_apply_differentiableAt`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.mongeAmpereConsistentAtBasepoint`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.normalizedKaehlerRicci_zero_implies_fixedpoint`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.ricci_tensor_invariant_at_fixed_point`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
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
- **`InfoGeometry.Canonical.RicciMongeAmpere.scalarRicci_invariant_at_fixed_point`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.spinorialScalarCurvature_eq_zero_of_normalized_fixedpoint`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.vacuumEinsteinAt_implies_on_transportedSplit`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.vacuumEinsteinEquation_of_spinorial_scalar`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RicciMongeAmpere.vacuumOnTransportedSplit_iff_curvature_action_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RobustThermodynamicRegression.lean`

- **`InfoGeometry.Canonical.FUSION.phase_transition_catastrophe`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RosettaScaleTransport.lean`

- **`InfoGeometry.Canonical.Rosetta.isJordanKKTGeometry_of_weylScaleTransportShadow`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Rosetta.kk_analyticalIndex_eq_of_weylScaleTransport`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Rosetta.weylScaleTransportScalarShadow_eq_jordanBregman_of_isJordanKKTGeometry`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RosettaSourceBridge.lean`

- **`InfoGeometry.Canonical.Rosetta.instCompleteSpaceVCl11DoubledCore`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/Singular.lean`

- **`InfoGeometry.Canonical.EinsteinAnomaly_eq_zero_of_regularization_pair`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.EinsteinAnomaly_eq_zero_of_selfAdjoint_idempotent`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.einsteinAnomaly_skew_adjoint`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.exists_drazinInverse_endomorphism_of_isUnit`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.exists_drazinInverse_of_idempotent`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.exists_moorePenroseInverse_endomorphism_of_isUnit`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.exists_moorePenroseInverse_of_isUnit`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.exists_moorePenroseInverse_of_selfAdjoint_idempotent`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.exists_regularization_pair_of_isUnit`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.exists_regularization_pair_of_selfAdjoint_idempotent`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/SingularBoundaryCorrection.lean`

- **`InfoGeometry.Canonical.SingularBoundaryCorrection.boundaryGenerator_eq_zero_of_projectors_commute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SingularBoundaryCorrection.projectors_commute_of_boundaryGenerator_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SingularBoundaryCorrection.rightBoundaryGenerator_eq_projector_commutator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/SingularTransportSystem.lean`

- **`InfoGeometry.Canonical.SingularTransportSystem.boundaryGenerator_eq_projector_commutator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SingularTransportSystem.boundaryGenerator_eq_zero_iff_projectors_commute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SingularTransportSystem.boundaryScale_eq_projectorObstruction_norm`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SingularTransportSystem.dilation_commutator_decomposes_boundaryGenerator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SingularTransportSystem.regular_radial_transport_closes_of_boundaryScale_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/SinkhornFoundation.lean`

- **`InfoGeometry.Canonical.MoE.SinkhornCertificate.leftScale_pos`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.SinkhornCertificate.rightScale_pos`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.bayesianFreeEnergyObjective_eq_regularizedOTObjective`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.colLyapunov_nonneg`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.colNormalize_has_unit_colMarginal`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.colRNBarrier_nonneg`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.entropicOptimalTransportObjective_eq_transport_plus_entropy`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.exists_perm_decomposition_of_sinkhornBalanced`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.gc_gibbsWeight_eq_normalizedWeights`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.gc_partition_eq_routerPartition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.kahlerPotentialRN_eq_scalarModularPotential_relativeVolumeChangeRN`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.relativeVolumeChangeRN_eq_exp_logJacobian`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.rn_barrier_row_step_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.rowLyapunov_nonneg`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.rowNormalize_has_unit_rowMarginal`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.rowRNBarrier_nonneg`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.schroedingerBridgeStep_monotone`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.schroedingerBridgeStep_radonNikodymBarrier_monotone`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.sinkhornScaledCoupling_def`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.sinkhornStep_bayesianFreeEnergy_monotone`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.sinkhornStep_entropicOT_monotone`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.sinkhornTwoStep_eq_bayesianPosteriorGauge`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.sinkhornTwoStep_eq_schroedingerBridgeGauge`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.switchMatrix_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.switchMatrix_mem_rowStochastic`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.MoE.trajectoryLyapunovNext_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/SinkhornKMSCore.lean`

- **`InfoGeometry.Canonical.KMSSinkhornBridge.kreinRouterModularHamiltonian_isKreinSelfAdjoint`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KMSSinkhornBridge.routerModularHamiltonian_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KMSSinkhornBridge.sinkhorn_stepwise_kms_bound`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/SpectralInference.lean`

- **`InfoGeometry.Canonical.SpectralInference.CertifiedChiralSpectralTriple.chiralAnomalyOperator_eq_zero_iff_projectors_commute`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.SpectralInference.CertifiedChiralSpectralTriple.epsilon_eq_zero_of_projectors_commute`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.SpectralInference.CertifiedChiralSpectralTriple.exists_of_spectralTriple`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.SpectralInference.CertifiedChiralSpectralTriple.metricProjector_idempotent`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.SpectralInference.CertifiedChiralSpectralTriple.metricProjector_star`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.SpectralInference.CertifiedChiralSpectralTriple.spectralProjector_idempotent`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.SpectralInference.CertifiedRegularizedSpectralTriple.exists_of_spectralTriple`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.SpectralInference.CertifiedRegularizedSpectralTriple.spectralProjector_idempotent`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Canonical.SpectralInference.InfoSpectralTriple.dirac_eq_canonicalDiracOfMetric_of_isPositive`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SpectralInference.InfoSpectralTriple.inner_dirac_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SpectralInference.SpectralTriple.is_self_adjoint`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SpectralInference.bayesianAction_nonneg`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SpectralInference.bayesianAction_succ`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SpectralInference.bayesianAction_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/SpinConnection.lean`

- **`InfoGeometry.Canonical.SpinConnection.U_add`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SpinConnection.U_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.transportEnd_add`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.transportEnd_lie`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.transportEnd_mul`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/SpinorModularBridge.lean`

- **`InfoGeometry.Canonical.SpinorModularBridge.SpinorModularIdentification.is_minus_dangling`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SpinorModularBridge.SpinorModularIdentification.is_minus_weyl`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SpinorModularBridge.SpinorModularIdentification.is_plus_dangling`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SpinorModularBridge.SpinorModularIdentification.is_plus_weyl`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SpinorModularBridge.boundaryGenerator_is_vorticity`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SpinorModularBridge.curvature_concentrated_on_dangling_modes`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SpinorModularBridge.horizon_is_scale_invariant`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/SplitCliffordThermalBridge.lean`

- **`InfoGeometry.Canonical.SplitCliffordThermalBridge.splitCliffordThermalBridge_of_strictSymmetry`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SplitCliffordThermalBridge.transportedThermalFlow_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SplitCliffordThermalBridge.transportedThermalGenerator_eq_transportDirac_of_zeroChemicalPotential`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/StandardFormCore.lean`

- **`InfoGeometry.Canonical.StandardFormCore.RelativeModularBridge.operatorLogPotential_add`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.StandardFormCore.RelativeModularBridge.projectiveModularPotential_eq_logDensity_target_sub_source`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.StandardFormCore.StandardFormSeed.J_phase_anticommute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.StandardFormCore.StandardFormSeed.J_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.StandardFormCore.StandardFormSeed.eps_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.StandardFormCore.VectorState.expectation_id`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.StandardFormCore.tomitaAtomSeed_J_comp_phaseAxis_eq_eps`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.StandardFormCore.tomitaAtomSeed_eps_comp_J_eq_neg_phaseAxis`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.StandardFormCore.tomitaAtomSeed_eps_comp_phaseAxis_eq_neg_J`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.StandardFormCore.tomitaAtomSeed_eps_eq_spectral_epsilon`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.StandardFormCore.tomitaAtomSeed_minusProjector_eq_spectralMinusProj`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.StandardFormCore.tomitaAtomSeed_minusProjector_mem_minusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.StandardFormCore.tomitaAtomSeed_modularFlow_eq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.StandardFormCore.tomitaAtomSeed_phaseAxis_comp_J_eq_neg_eps`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.StandardFormCore.tomitaAtomSeed_phaseAxis_comp_eps_eq_J`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.StandardFormCore.tomitaAtomSeed_phaseAxis_eq_J_comp_eps`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.StandardFormCore.tomitaAtomSeed_phaseAxis_eq_dilationOperator`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_eq_dilationOperator`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.StandardFormCore.tomitaAtomSeed_phaseAxis_sq_expectation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.StandardFormCore.tomitaAtomSeed_plusProjector_eq_spectralPlusProj`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.StandardFormCore.tomitaAtomSeed_plusProjector_mem_plusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/StateDependentTransport.lean`

- **`InfoGeometry.Canonical.StateDependentTransport.constantStateModularDatum_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.StateDependentTransport.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.StateDependentTransport.stateModularSeed_eq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.StateDependentTransport.stateQGTMetricReadout_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.StateDependentTransport.stateQGTPhaseReadout_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.StateDependentTransport.stateQGTReadout_constant_pair_eq_zero_of_relativeModularDeriv_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.StateDependentTransport.stateRelativeModularGenerator_constant`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.StateDependentTransport.stateTransportGenerator_eq_relativeModularKGenerator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/SuperAnomaly.lean`

- **`InfoGeometry.Canonical.SuperAnomaly.SuperWeightLike.graded_weight_anticommutator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperAnomaly.SuperWeightLike.graded_weight_commutator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperAnomaly.superComm_even_left`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/SuperInference.lean`

- **`InfoGeometry.Canonical.SuperInference.superCharge_boson_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperInference.superCharge_fermion_eq_dualMap`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperInference.susyHamiltonian_eq_self`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/SuperJordanLie.lean`

- **`InfoGeometry.Canonical.SuperJordanLie.fockAnticommutator_eq_two_smul_jordanProduct`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperJordanLie.fockCommutator_eq_two_smul_lieProduct`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperJordanLie.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperJordanLie.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
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
- **`InfoGeometry.SuperUnified.hamiltonian_is_bosonic`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.SuperUnified.symplectic_is_complex_structure`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/SuperchargeTransportBridge.lean`

- **`InfoGeometry.Canonical.SuperchargeTransportBridge.deriv2_transportedParitySupercharge_at_zero_eq_metricPart_add_half_curvaturePart`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeTransportBridge.deriv2_transportedParitySupercharge_at_zero_eq_operatorInformationHessian`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeTransportBridge.deriv2_transportedParitySupercharge_at_zero_eq_operatorInformationMetricPart`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeTransportBridge.deriv_anticommutator_transportedParity_staticModular_at_zero_eq_phaseAntilinearSeed_of_commute_phaseLinearPart`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeTransportBridge.deriv_anticommutator_transportedParity_staticModular_at_zero_eq_zero_of_commute_modularJ`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeTransportBridge.deriv_transportedModularSupercharge`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeTransportBridge.deriv_transportedModularSupercharge_at_zero_eq_phaseAntilinear_of_commute_phaseLinearPart`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeTransportBridge.deriv_transportedParitySupercharge`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeTransportBridge.deriv_transportedParitySupercharge_at_zero_eq_phaseAntilinear_of_commute_phaseLinearPart`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeTransportBridge.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeTransportBridge.parity_modular_anticommutator_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeTransportBridge.transportedModularSupercharge_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeTransportBridge.transportedParitySupercharge_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ThermodynamicAction.lean`

- **`InfoGeometry.Canonical.ThermodynamicAction.fisherInformationMetric_eq_comparisonGeneratorMetric`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ThermodynamicAction.operatorialKLDivergence_eq_functionalShift`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ThermodynamicGenerator.lean`

- **`InfoGeometry.Canonical.ThermodynamicGenerator.apply_operatorialGrandCanonicalWeight_eq_informationPartitionFunction`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ThermodynamicGenerator.comparisonReadout_pair_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ThermodynamicGenerator.deriv_apply_operatorialGibbsWeight_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ThermodynamicGenerator.firstVariation_eq_gaugeVariation_add_sourceVariation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ThermodynamicGenerator.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ThermodynamicGenerator.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace_1`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ThermodynamicGenerator.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace_2`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ThermodynamicGenerator.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace_2`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ThermodynamicGenerator.isThermodynamicReadoutStationary_iff_firstVariation_eq_zero_of_probeFaithful`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ThermodynamicGenerator.liftedChiralAnomalyMassieuPotential_normalizedInfinitesimalLaw`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ThermodynamicGenerator.liftedEinsteinAnomalyMassieuPotential_normalizedInfinitesimalLaw_of_projectorAgreement`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ThermodynamicGenerator.liftedProjectorObstructionMassieuPotential_normalizedInfinitesimalLaw`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ThermodynamicGenerator.operatorialGibbsWeight_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ThermodynamicGenerator.souriauTemperatureVector_eq_generator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ThermodynamicGenerator.souriauTemperatureVector_eq_stateRelativeModularGenerator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ThermodynamicGenerator.souriauTemperatureVector_eq_transportGenerator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ThermodynamicGenerator.stateRelativeGrandCanonicalGenerator_eq_generator_of_vacuumTransported`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ThermodynamicGenerator.stateRelativeGrandCanonicalGenerator_eq_generator_of_zeroChemicalPotential`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ThermodynamicGenerator.stateRelativeGrandCanonicalMassieuPotential_normalizedInfinitesimalLaw_of_vacuumTransported`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ThermodynamicGenerator.stateRelativeGrandCanonicalMassieuPotential_normalizedInfinitesimalLaw_of_zeroChemicalPotential`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ThermodynamicGenerator.toRelationalInformationDatum_comparisonMetricPhase_pair_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/TomitaTakesaki.lean`

- **`InfoGeometry.Canonical.TomitaTakesaki.cptAtoms_generate_splitCliffordAlg`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.cptJ_cptJeps_anticommute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.cptJ_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.cptJeps_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.modularCPTSupercharge_Q_eq_dilationOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.modularCPTSupercharge_hamiltonian`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.modularCPTSupercharge_maps_minus_to_plus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.modularCPTSupercharge_maps_plus_to_minus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.modularCPT_supergraded_lie_package`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ_commutator_modularSignEpsilon`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.modularFlow_reversal`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ_exp_modularComplexI`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.modularOperator_inversion`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.modularSignAdditiveModularFlow_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.tomitaRepresentation_cptEps`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.tomitaRepresentation_cptJ`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.TomitaTakesaki.tomitaRepresentation_cptJeps`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/TopologicalEuler.lean`

- **`InfoGeometry.Canonical.TopologicalEuler.euler_is_invariant`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/TopologicalInvariants.lean`

- **`InfoGeometry.Canonical.TopologicalInvariants.chiralAnomalyIndex_eq_zero_of_projectors_commute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/TopologicalResidue.lean`

- **`InfoGeometry.Canonical.TopologicalResidue.witten_index_invariant_under_onsager_flow`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/TransportLieDerivative.lean`

- **`InfoGeometry.Canonical.DifferentiableSpinConnection.U_differentiable`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DifferentiableSpinConnection.U_inv_differentiable`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KAxis.orthogonal`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KAxis.skew`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularCPTChiralAtom.J_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularCPTChiralAtom.K_orthogonal`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularCPTChiralAtom.K_skew`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularCPTChiralAtom.anticomm`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularCPTChiralAtom.eps_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.axisAntilinearPart_eq_self_of_isAxisAntilinear`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.axisAntilinearPart_eq_zero_of_isAxisLinear`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.axisLinearPart_eq_self_of_isAxisLinear`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.axisLinearPart_eq_zero_of_isAxisAntilinear`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.complexLike_i_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.deriv_expTransport`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.deriv_expTransportEnd_at_zero_eq_zero_of_commute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.deriv_expTransport_at_zero_eq_zero_of_commute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.deriv_hestenesTransport_at_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.hasDerivAt_expTransportEnd_at_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.lieDerivEnd_eq_commutator_generator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.lieDerivEnd_eq_zero_of_commute_generator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.lieDerivMetric_eq_zero_of_commute_generator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.lieDerivMetric_eq_zero_of_commute_generator_of_commute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.metricOfOperator_add`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.modularAxisLinearPart_add_modularAxisAntilinearPart`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.transportGenerator_eq_of_exp_flow`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/Triality.lean`

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
- **`InfoGeometry.Canonical.Triality.splitMetricTriadicInstance_route_norm_compat`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/TwistorOperatorialIncidence.lean`

- **`InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.operatorialIncidence_iff_projectorObstructionOperator_zero`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`

### `lean/InfoGeometry/Canonical/Unification.lean`

- **`InfoGeometry.Canonical.Unification.AnomalyRosettaStone.h_geo_thermo`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Unification.AnomalyRosettaStone.h_thermo_alg`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Unification.Cl11LatticeRosettaStone.continuous_eq_lattice_shadow`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Unification.instCompleteSpaceContinuousLinearMapRealIdContinuousCarrier`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Unification.instIsTopologicalRingContinuousLinearMapRealIdContinuousCarrier`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Unification.scalarToFockLift_add_const_eq_centralGaugeShift`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/VariationalLadder.lean`

- **`InfoGeometry.Canonical.VariationalLadder.onsager_reciprocity_at_comparison`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/VolumeDeformationPrinciple.lean`

- **`InfoGeometry.Canonical.VolumeDeformationPrinciple.DefectiveVolumeBridge.potential_mul`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.VolumeDeformationPrinciple.ExactVolumeBridge.potential_mul`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.VolumeDeformationPrinciple.ExactVolumeBridge.potential_mulCommutator_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/VortexAnomalyLink.lean`

- **`InfoGeometry.Canonical.VortexAnomalyLink.VortexPair.sink_comm_eps`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.VortexAnomalyLink.VortexPair.sink_idem`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.VortexAnomalyLink.VortexPair.sink_source_orth`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.VortexAnomalyLink.VortexPair.source_comm_eps`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.VortexAnomalyLink.VortexPair.source_idem`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.VortexAnomalyLink.VortexPair.source_sink_orth`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.VortexAnomalyLink.canonicalSinkBoundarySupercharge_projectedNilpotent`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.VortexAnomalyLink.canonicalSinkBoundarySupercharge_sq_eq_zero`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.VortexAnomalyLink.canonicalSourceBoundarySupercharge_projectedNilpotent`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.VortexAnomalyLink.canonicalSourceBoundarySupercharge_sq_eq_zero`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.VortexAnomalyLink.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.VortexAnomalyLink.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.VortexAnomalyLink.sinkVortexSeed_comp_J_eq_J_comp_sourceVortexSeed_of_commute_modularJ`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.VortexAnomalyLink.sinkVortexSeed_eq_neg_minusProjectorFlux`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.VortexAnomalyLink.sourceVortexSeed_add_sinkVortexSeed_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.VortexAnomalyLink.sourceVortexSeed_comp_J_eq_J_comp_sinkVortexSeed_of_commute_modularJ`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.VortexAnomalyLink.sourceVortexSeed_eq_neg_plusProjectorFlux`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/VortexReferenceGaugeBridge.lean`

- **`InfoGeometry.Canonical.VortexReferenceGaugeBridge.comparisonMetricReadout_eq_of_sinkSectorDegeneracy`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.VortexReferenceGaugeBridge.comparisonMetricReadout_eq_of_sourceSectorDegeneracy`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.VortexReferenceGaugeBridge.comparisonPhaseReadout_eq_of_sinkSectorDegeneracy`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.VortexReferenceGaugeBridge.comparisonPhaseReadout_eq_of_sourceSectorDegeneracy`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.VortexReferenceGaugeBridge.functionalShift_eq_of_sinkSectorDegeneracy`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.VortexReferenceGaugeBridge.functionalShift_eq_of_sourceSectorDegeneracy`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.VortexReferenceGaugeBridge.twoStateGap_eq_of_sinkSectorDegeneracy`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.VortexReferenceGaugeBridge.twoStateGap_eq_of_sourceSectorDegeneracy`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/WeightedWeylNormalizationBridge.lean`

- **`InfoGeometry.Canonical.WeightedWeylNormalizationBridge.densityWeightLiftedReadout_pair_eq_zeroWeight_add_weighted_phaseAxisReadout`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/WeylAnomalySource.lean`

- **`InfoGeometry.Canonical.WeylInformationGauge.nonzeroAnomaly_sources_transportedEinsteinResidual`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/WeylGaugeField.lean`

- **`InfoGeometry.Canonical.WeylDifferentialOperator.map_add_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylDifferentialOperator.map_smul_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylDifferentialOperator.map_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
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
- **`InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.liftedOperator_referenceTransport_eq_gauge_smul_epsilonBoost`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.logRelativeVolumePotential_eq_two_mul_relativeLogCoordinate`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.logRelativeVolumePotential_mulTransport`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.minusBlockMap_liftedOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.minusProjectorFlux_liftedOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.minusToPlusBlockMap_liftedOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.plusBlockMap_liftedOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.plusProjectorFlux_liftedOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.plusToMinusBlockMap_liftedOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeOperatorLift.LiftedSheetAut.relativeVolumeScale_gaugeRescale`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/WeylPathHysteresis.lean`

- **`InfoGeometry.Canonical.WeylInformationGauge.twistedInference_updateOrderPathDependent`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylInformationGauge.weylOrderWitnessMatrix2_positiveCols_afterRow`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylInformationGauge.weylOrderWitnessMatrix2_positiveRows_afterCol`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

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
- **`InfoGeometry.Canonical.WeylGaugeField.respondCovariantFlow_transform_eq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeField.responseAlong_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylGaugeField.responseAlong_eq_along_comp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylLineIntegrator.gaugeCompensatedHolonomy_eq_base_of_boundary_law`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylLineIntegrator.integrateCurvature_transformByPotential_eq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/WeylTransportChiralBridge.lean`

- **`InfoGeometry.Canonical.WeylTransportBridge.finiteSum_holonomy_eq_chiralScale_of_flat`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylTransportBridge.finiteSum_holonomy_eq_projectorObstruction_nnnorm_of_flat`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylTransportBridge.holonomy_eq_chiralScale_of_flat`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylTransportBridge.holonomy_eq_chiralScale_of_flat_of_projectorObstructionBridge`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WeylTransportBridge.holonomy_eq_zero_of_flat_of_unitRelativeVolume`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/YangMillsContinuum.lean`

- **`InfoGeometry.Canonical.YangMillsContinuum.IBSampledFlow.sinkhornClosure_of_sampledIB`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.YangMillsContinuum.IBSampledFlow.sinkhornClosure_of_sampledIB_components`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.TypeIIIModularInterface.infinitesimal_generator_at_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.TypeIIIModularInterface.modularAutomorphismGroup_additive`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.TypeIIIModularInterface.modularHamiltonian_eq_neg_log_rn`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.TypeIIIModularInterface.modularOperator_eq_rn`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.connesRovelliThermalTimeIdentity`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.deriv_modularAutomorphismGroup_zero_eq_commutator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.deriv_modularShift_zero_eq_commutator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.modularAutomorphismGroup_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
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
- **`InfoGeometry.Canonical.YangMillsFinite.FiniteYangMillsBridge.obligations_of_expectationSeedFromLogDet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ZetaDeterminant.lean`

- **`InfoGeometry.Canonical.Determinant.SpectralZetaLogDetData.cutoff_ne_zero'`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Determinant.SpectralZetaLogDetData.logDet_eq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Determinant.capstone_logAbsVolume_add_from_zeta`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.Determinant.zetaRegularizedLogVolume_add`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.Determinant.spectralZetaLogDetDataOfChiralTriple_logDet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Determinant.spectralZetaLogDetDataOfRegularizedTriple_logDet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Determinant.zetaRegularizedLogDet_eq_logAbsDet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Determinant.zetaRegularizedLogDet_mul`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Determinant.zetaRegularizedLogVolume_eq_logAbsVolume`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Clifford/Lift.lean`

- **`InfoGeometry.Clifford.Lift.Q11_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Clifford.Lift.cl11RepLin_apply_pair`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`, `rfl-like`

### `lean/InfoGeometry/Clifford/NeutralPhaseSpaceDoubledBridge.lean`

- **`InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge.canonicalNeutralFormUnscaled_realizeToDoubledRho`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge.modularRotation_to_doubled`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge.phaseEpsilonEquiv_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge.phaseEpsilonEquiv_toLinearMap`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge.phaseEpsilon_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge.phaseEpsilon_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge.phaseJEquiv_phaseEpsilonEquiv_anticommute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge.phaseJEquiv_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge.phaseJEquiv_toLinearMap`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge.phaseJ_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge.phaseJ_phaseEpsilon_anticommute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge.phaseJ_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge.phaseRotationEquiv_toLinearMap`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge.toDoubledCopyRho_comp_phaseEpsilon`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/KK/ClNNFredholmBridge.lean`

- **`InfoGeometry.KK.ClNNFredholmBridge.RealSplitKreinKasparovCycle.firstStep_leftGenerator_eq_cl11Rep`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.KK.ClNNFredholmBridge.RealSplitKreinKasparovCycle.firstStep_pseudoscalar_eq_cl11Rep`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.KK.ClNNFredholmBridge.RealSplitKreinKasparovCycle.firstStep_rightGenerator_eq_cl11Rep`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/KK/CompactOperatorBridge.lean`

- **`InfoGeometry.KK.isCompactEnd_of_finiteDimensional`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.KK.isCompactEnd_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/KK/RealSplitKKTBridge.lean`

- **`InfoGeometry.KK.RealSplitKKTBridge.F_eq_gOnePart_add_gNegOnePart_of_gradeCLM_eq_eps`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.KK.RealSplitKKTBridge.gZeroPart_F_eq_zero_of_gradeCLM_eq_eps`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.KK.RealSplitKKTBridge.pi_isGZero_of_gradeCLM_eq_eps`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.KK.RealSplitKKTBridge.rho_isGZero_of_gradeCLM_eq_eps`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Krein/HilbertBridge.lean`

- **`InfoGeometry.Krein.HilbertDoubled.coe_toLp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.HilbertDoubled.ext_iff`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.HilbertDoubled.fst_ofWithLp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.HilbertDoubled.fst_toLp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
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
- **`InfoGeometry.Krein.NeutralSpace.ext_iff`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.NeutralSpace.fst_coe`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.NeutralSpace.fst_ofWithLp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.NeutralSpace.fst_toLp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.NeutralSpace.fst_val`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
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

### `lean/InfoGeometry/MaxEnt/DualBridge.lean`

- **`InfoGeometry.MaxEnt.gibbs_form_candidate_maximizes_entropy`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.MaxEnt.gibbs_maximizes_entropy_on_constraint`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.MaxEnt.gibbs_mem_maxEntConstraint_iff`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.MaxEnt.momentResidual_eq_zero_iff`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Projective/Bridge.lean`

- **`InfoGeometry.Projective.interiorToPositiveMeasure_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Projective.mem_interior_positiveOrthantCone_iff`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Projective.projectiveClassToConeInteriorStateSpace_mk`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/AttentionBridge.lean`

- **`InfoGeometry.Quantum.AttentionBridge.attention_source_transports_to_modular`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.AttentionBridge.split_attention_as_residual`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.AttentionBridge.split_softmax_weight_formula`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/BulkBoundary.lean`

- **`InfoGeometry.Quantum.BulkBoundary.BoundaryLocalizedZeroModeWitness.psiMinus_mem`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.BulkBoundary.BoundaryLocalizedZeroModeWitness.psiMinus_ne_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.BulkBoundary.BoundaryLocalizedZeroModeWitness.psiMinus_zeroMode`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.BulkBoundary.BoundaryLocalizedZeroModeWitness.psiPlus_mem`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.BulkBoundary.BoundaryLocalizedZeroModeWitness.psiPlus_ne_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.BulkBoundary.BoundaryLocalizedZeroModeWitness.psiPlus_zeroMode`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
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
- **`InfoGeometry.Quantum.CommutingInvolutionCore.je_comm`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.CommutingInvolutionCore.je_def`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.CommutingInvolutionCore.je_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/Fierz.lean`

- **`InfoGeometry.Quantum.Fierz.information_fierz_majorana`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/Fock.lean`

- **`InfoGeometry.Quantum.annihilation_kills_vacuum_vector`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.bayesianAddData_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.bayesian_update_preserves_data_independence`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.commutator_I_J`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.commutator_J_epsilon_eq_two_I`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.creation_annihilation_orthogonal`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.data_model_decomposition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.vacuum_is_zero_ray`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean`

- **`InfoGeometry.Quantum.GeometricQuantumTensor.berryTwoFormJEpsOfOperator_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.berryTwoFormJEpsOfOperator_apply_eq_berryOfOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.berryTwoFormJEpsOfOperator_liftedEinsteinAnomalyOperator_eq_neg_liftedProjectorObstructionOperator_of_projectorAgreement`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.deriv_berryOfOperator_liftedEinsteinAnomalyOperator_relativeModularTransport_eq_berryOfOperator_expTransport_relativeModularSourceDeriv_of_commute_gaugePart`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.deriv_berryOfOperator_modularTransport_conjugation_at_zero_eq_berryOf_modularGaugeDeriv_add_berryOf_relativeModularSourceDeriv`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.deriv_berryOfOperator_modularTransport_conjugation_eq_berryOfOperator_expTransport_modularGaugeDeriv_add_berryOfOperator_expTransport_relativeModularSourceDeriv`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.deriv_berryTwoFormJEpsOfOperator_liftedEinsteinAnomalyOperator_relativeModularTransport_eq_berryTwoFormJEpsOf_expTransport_relativeModularSourceDeriv_of_commute_gaugePart`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.deriv_berryTwoFormJEpsOfOperator_modularTransport_conjugation_at_zero_eq_berryTwoFormJEpsOf_relativeModularDeriv`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.deriv_berryTwoFormJEpsOfOperator_modularTransport_conjugation_eq_berryTwoFormJEpsOf_expTransport_relativeModularDeriv`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.deriv_berryTwoFormJEpsOfOperator_projectorObstructionOperator_relativeModularTransport_at_zero_eq_berryTwoFormJEpsOf_relativeModularSourceDeriv_of_commute_gaugePart`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.deriv_berryTwoFormJEpsOfOperator_projectorObstructionOperator_relativeModularTransport_eq_berryTwoFormJEpsOf_expTransport_relativeModularSourceDeriv_of_commute_gaugePart`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.deriv_metricOfOperator_modularTransport_conjugation_at_zero_of_commute_relativeModularKGenerator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.deriv_metricOfOperator_starCertified_liftedEinsteinAnomalyOperator_relativeModularTransport_at_zero_eq_metricOf_relativeModularSourceDeriv_of_commute_gaugePart`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.isPhaseLinear_modularComplexI_comp_liftedEinsteinAnomalyOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.isSelfAdjoint_modularComplexI_comp_liftedEinsteinAnomalyOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.qgtOfOperator_modularSignEpsilon_comp_berry_eq_kreinQgtOfOperator_berry`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.qgtOfOperator_modularSignEpsilon_comp_metric_eq_kreinQgtOfOperator_metric`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.qgtOfOperator_modularVarianceSeed_realizes_modularVariance`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/GeometricTensorTransport.lean`

- **`InfoGeometry.Quantum.GeometricQuantumTensor.berryTwoFormJEpsOfOperator_KRotation_eq_of_commute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.berryTwoFormJEpsOfOperator_modularTransportFlow_eq_of_commute_generator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.berryTwoFormJEpsOfOperator_modularTransportFlow_eq_of_generator_eq_smul_phaseAxis`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.kreinMetricOfOperator_modularTransportFlow_eq_of_generator_eq_smul_phaseAxis`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.kreinQgtOfOperator_modularTransportFlow_invariant_of_generator_eq_smul_phaseAxis`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator_liftedEinsteinAnomalyOperator_modularTransportFlow_eq_of_commute_generator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator_modularTransportFlow_eq_of_generator_eq_smul_phaseAxis`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator_modularTransport_infinitesimal_eq_gauge_channel_of_commute_scalePart`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator_modularTransport_infinitesimal_eq_scale_channel_of_commute_gaugePart`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator_modularTransport_infinitesimal_stationary_of_commute_generator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.qgtOfOperator_modularTransportFlow_invariant_of_commute_generator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.qgtOfOperator_modularTransportFlow_invariant_of_generator_eq_smul_phaseAxis`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/HestenesKahler.lean`

- **`InfoGeometry.Quantum.BigradedOperator.hasPhaseParity`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.PhaseGradedOperator.hasParity`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ProjectivePolarizedBigradedBogoliubovDatum.K_maps_minus_to_plus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ProjectivePolarizedBigradedBogoliubovDatum.K_maps_plus_to_minus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ProjectivePolarizedBigradedBogoliubovDatum.aPlus_sub_aMinus_eq_polarization`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ProjectivePolarizedBigradedBogoliubovDatum.compat`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ProjectivePolarizedBigradedBogoliubovDatum.isProjectorSuperPair_aMinus_aPlus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ProjectivePolarizedBigradedBogoliubovDatum.ray_eq_of_smul_representative`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.certifiedProjectorObstructionAxis_bidegree`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Quantum.certifiedProjectorObstructionStateInducedDynamics_eq_gauge_add_source`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Quantum.certifiedProjectorObstructionStateInducedDynamics_eq_relativeModularDeriv`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Quantum.certifiedProjectorObstructionStateMetricReadout_eq_hestenesMetricTwoForm`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Quantum.certifiedProjectorObstructionStatePhaseReadout_eq_hestenesBerryTwoForm`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Quantum.certifiedProjectorObstructionStatePhaseReadout_eq_metric_comp_K`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Quantum.phaseAxisForce_phase_odd`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.starCertifiedEinsteinAnomalyAxis_bidegree`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Quantum.starCertifiedEinsteinAnomalyStateInducedDynamics_eq_gauge_add_source`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Quantum.starCertifiedEinsteinAnomalyStateInducedDynamics_eq_relativeModularDeriv`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Quantum.starCertifiedEinsteinAnomalyStateMetricReadout_eq_hestenesMetricTwoForm`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Quantum.starCertifiedEinsteinAnomalyStatePhaseReadout_eq_hestenesBerryTwoForm`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Quantum.starCertifiedEinsteinAnomalyStatePhaseReadout_eq_metric_comp_K`** — `V2/dead-public-theorem`
  - Tags: `certified-surface`, `dead-candidate`
- **`InfoGeometry.Quantum.weldedProjectorObstructionAxis_bidegree`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.weldedProjectorObstructionBerry_eq_zero_of_operatorialIncidence`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.weldedProjectorObstruction_pairedSourceCancellation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.weldedProjectorObstruction_state_split`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/Hurwitz.lean`

- **`InfoGeometry.Quantum.Hurwitz.K_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.Hurwitz.card_hurwitzDirections`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.Hurwitz.supercharge_sq_eq_laplacian`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/HurwitzRGFlow.lean`

- **`InfoGeometry.Quantum.HurwitzRGFlow.HurwitzShellAction.betaFunction_eq_zero_of_invariantAtScale`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/InvolutionCore.lean`

- **`InfoGeometry.Quantum.InvolutionCore.je_def`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/KitaevChain.lean`

- **`InfoGeometry.Quantum.KitaevChain.KitaevCell.is_skew`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.KitaevChain.KitaevCocycle.cocycle`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.KitaevChain.hasDefect_singleton_iff_isCritical`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
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
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ModularAnomaly.Cl11LatticeBridge.latticeAvatarCLM_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ModularAnomaly.Cl11LatticeBridge.latticeAvatar_exp_modularConjugationJ`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ModularAnomaly.Cl11LatticeBridge.latticeMatrixCLM_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ModularAnomaly.Cl11Shadow.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ModularAnomaly.Cl11Shadow.modularAnomalyGenerator_eq_exp_commutator_shadow`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ModularAnomaly.Lattice.anomaly_free_blockA_is_orthogonal`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ModularAnomaly.Lattice.blockD_sigmaMatrix`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ModularAnomaly.Lattice.det_sigmaLDUProduct_eq_one_of_factorization`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
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
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ModularAnomaly.TopologicalMajoranaShadow.J_conj_sigma`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ModularAnomaly.TopologicalMajoranaShadow.einstein_anomaly_is_modular_generator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ModularAnomaly.TopologicalMajoranaShadow.modularCocycle_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ModularAnomaly.TopologicalMajoranaShadow.sigma_add`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/ProjectiveRayBridge.lean`

- **`InfoGeometry.Quantum.ProjectiveRayBridge.same_ray_incidence_left`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ProjectiveRayBridge.same_ray_incidence_right`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/QuantumGeometryProjectorBridge.lean`

- **`InfoGeometry.Quantum.deriv_berryTwoFormJEpsOfOperator_quantumGeometryEinsteinTransportedOperatorPair_at_zero_eq_berryTwoFormJEpsOf_relativeModularSourceDeriv_pair_of_commute_gaugePart`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.deriv_comparisonTransportPhaseShiftedChannelCorrelation_liftedProjectorObstructionCorrelationSeed_at_zero_eq_comparisonMetricReadout_snd_quantumGeometryProjectorOperatorPair`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.deriv_fst_quantumGeometryEinsteinTransportedOperatorPair_at_zero_eq_relativeModularSourceDeriv_of_commute_gaugePart`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.deriv_quantumGeometryEinsteinTransportedOperatorPair_at_zero_eq_comparisonStateGeneratorMetricPhase_source_pair_of_commute_gaugePart`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.deriv_quantumGeometryEinsteinTransportedOperatorPair_at_zero_eq_stateQGTReadout_constant_pair`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.deriv_snd_quantumGeometryEinsteinTransportedOperatorPair_at_zero_eq_relativeModularSourceDeriv_of_commute_gaugePart`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.fst_quantumGeometryProjectorOperatorPair`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.minusProjectorFlux_fst_quantumGeometryProjectorOperatorPair`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.minusProjectorFlux_snd_quantumGeometryProjectorOperatorPair`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.plusProjectorFlux_fst_quantumGeometryProjectorOperatorPair`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.plusProjectorFlux_snd_quantumGeometryProjectorOperatorPair`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.quantumGeometryMetric_and_weldedProjectorPhase_eq_comparisonMetricPhase`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.quantumGeometryMetric_and_weldedProjectorPhase_eq_metricOfOperator_pair_of_projectorAgreement`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.snd_quantumGeometryProjectorOperatorPair`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/RealKCategory.lean`

- **`InfoGeometry.Quantum.RealKCategory.RealKVect.Hom.comm`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealKCategory.RealKVect.Hom.ext_iff`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
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
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.KPolarization.Hom.intertwines`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.KPolarization.P_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.KPolarization.PolarizationSplit.Hom.ext_iff`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
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
  - Tags: `dead-candidate`
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
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.PolarizedMajorana.Hom.gamma_intertwines`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.PolarizedMajorana.Hom.toBogoliubovTransform_preservesPolarization`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
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
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.RealBogoliubovTransform.transportPi_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum.K_ne_Pi`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum.car_realization_of_clifford`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum.chiralityPolarization_minus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum.chiralityPolarization_plus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/RealMajoranaCategory.lean`

- **`InfoGeometry.Quantum.RealMajoranaCategory.Polarization.involution_ofInvolution`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
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
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajoranaCategory.PolarizedMajorana.hom_comp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajoranaCategory.PolarizedMajorana.hom_id`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajoranaCategory.RealMajoranaCore.Hom.comm_Pi`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajoranaCategory.RealMajoranaCore.Hom.ext_iff`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajoranaCategory.RealMajoranaCore.hom_comp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajoranaCategory.RealMajoranaCore.hom_id`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajoranaCategory.majorana_car_of_concrete_cl11`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajoranaCategory.spectralMinusProj_comm_Pi`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RealMajoranaCategory.spectralPlusProj_comm_Pi`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/RealSplitClifford.lean`

- **`InfoGeometry.Quantum.doubledSpaceCl11Action_J`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.doubledSpaceCl11Action_K`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.doubledSpaceCl11Action_eps`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/RosettaSynthesis.lean`

- **`InfoGeometry.Quantum.RosettaSynthesis.instCompleteSpaceVCl11DoubledCore`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RosettaSynthesis.rosetta_anomaly_free_triality`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RosettaSynthesis.rosetta_source_tension_synthesis`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/SplitCliffordAtom.lean`

- **`InfoGeometry.Quantum.SplitCliffordAtom.Atom.Hom.comm_eps`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.SplitCliffordAtom.Atom.Hom.comm_j`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.SplitCliffordAtom.Atom.Hom.comm_k`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.SplitCliffordAtom.Atom.Hom.ext_iff`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.SplitCliffordAtom.Atom.hom_comp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.SplitCliffordAtom.Atom.hom_id`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/SplitTrialityFockBridge.lean`

- **`InfoGeometry.Quantum.SplitTrialityFockBridge.trialitySupercharge_square_eq_id_via_cliffordConcreteCAR`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/SplitTrialityKernel.lean`

- **`InfoGeometry.Quantum.SplitTrialityKernel.minus_comp_trialitySupercharge_eq_left`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.SplitTrialityKernel.plus_comp_trialitySupercharge_eq_right`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.SplitTrialityKernel.trialitySupercharge_sq_eq_id`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.canonicalSplitTrialityKernel.paritySupercharge_hamiltonian_parityEven`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/SuperchargeMultiplet.lean`

- **`InfoGeometry.Quantum.SuperchargeMultiplet.modular_comp_parity_eq_neg_complexI`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.SuperchargeMultiplet.modular_hamiltonian_eq_id`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.canonicalSuperchargeMultiplet.modular_eq_epsilonSupercharge`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.canonicalSuperchargeMultiplet.modular_hamiltonian_eq_id`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.epsilonSupercharge_hamiltonian`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.canonicalSuperchargeMultiplet.parity_eq_triality`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.canonicalSuperchargeMultiplet.parity_hamiltonian_eq_id`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.canonicalSplitTrialityKernel.paritySupercharge_hamiltonian_eq_id`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Quantum.canonicalSuperchargeMultiplet.parity_modular_anticommutator_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.canonicalSuperchargeMultiplet.phaseChannel_eq_complexI`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.canonicalSuperchargeMultiplet.phaseChannel_sq_eq_neg_id`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

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
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/TriadicTransportProjective.lean`

- **`InfoGeometry.Quantum.TriadicTransport.Update_content_proj_stable`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.TriadicTransport.Update_weight_proj_stable`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/TriadicWeylBridge.lean`

- **`InfoGeometry.Quantum.TriadicWeylBridge.dyadicKrein_isWeylCompatible_of_mem_minusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.TriadicWeylBridge.dyadicKrein_isWeylCompatible_of_mem_plusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.TriadicWeylBridge.eq_logarithmicGenerator_of_scalarSheetBlocks`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.TriadicWeylBridge.isWeylCompatible_iff_commutes_spectralMinusProj`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.TriadicWeylBridge.isWeylCompatible_iff_commutes_spectralPlusProj`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.TriadicWeylBridge.isWeylCompatible_iff_comp_spectralEpsilon`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.TriadicWeylBridge.triadicGenerator_blockDiagonal_of_compatibility`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/ZeroPointEnergy.lean`

- **`InfoGeometry.Quantum.ZeroPointEnergy.SpinFactorState.domain_valid`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.ZeroPointEnergy.zero_point_energy_topological_obstruction`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

## Most-Affected Files (top 20)

| File | Violations |
|------|------------|
| `lean/InfoGeometry/Canonical/BerryConnection.lean` | 32 |
| `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean` | 31 |
| `lean/InfoGeometry/Quantum/RealMajorana.lean` | 31 |
| `lean/InfoGeometry/Canonical/TransportLieDerivative.lean` | 28 |
| `lean/InfoGeometry/Core/SymmetricLieSpaces.lean` | 28 |
| `lean/InfoGeometry/Canonical/RicciMongeAmpere.lean` | 27 |
| `lean/InfoGeometry/MaxEnt/Jaynes.lean` | 27 |
| `lean/InfoGeometry/Canonical/SinkhornFoundation.lean` | 26 |
| `lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean` | 25 |
| `lean/InfoGeometry/Krein/HilbertBridge.lean` | 25 |
| `lean/InfoGeometry/Quantum/HestenesKahler.lean` | 25 |
| `lean/InfoGeometry/Thermal/FiniteMatrix.lean` | 25 |
| `lean/InfoGeometry/Canonical/RelativeModularSingularization.lean` | 24 |
| `lean/InfoGeometry/Canonical/RestrictedSheetContinuous.lean` | 24 |
| `lean/InfoGeometry/Canonical/MongeAmpereDualSheetBridge.lean` | 22 |
| `lean/InfoGeometry/Canonical/GrandCanonicalExperts.lean` | 21 |
| `lean/InfoGeometry/Canonical/ThermodynamicGenerator.lean` | 21 |
| `lean/InfoGeometry/Canonical/TomitaTakesaki.lean` | 21 |
| `lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean` | 20 |
| `lean/InfoGeometry/Canonical/IBUpdate.lean` | 20 |
