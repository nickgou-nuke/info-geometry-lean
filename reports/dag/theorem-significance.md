# Declaration Vacuity Triage Report

**Declarations scored:** 9615  
**With violations:** 3461 (715 error, 2746 warning-only)  
**Clean:** 6154  

## Tag Distribution

| Tag | Count |
|-----|-------|
| `dead-candidate` | 5525 |
| `proof-infrastructure` | 3802 |
| `auto-generated` | 2203 |
| `certified-surface` | 527 |
| `statement-bearing` | 288 |
| `rfl-like` | 274 |
| `role-exempt` | 159 |
| `high-fan-in` | 126 |
| `wrapper-candidate` | 118 |
| `attr:capstone` | 94 |
| `attr:infrastructure` | 38 |
| `attr:expository` | 26 |
| `capstone-candidate` | 4 |
| `attr:terminal` | 1 |

## Violation Distribution

| Violation | Count |
|-----------|-------|
| `V2/dead-public-theorem` | 3385 |
| `V1/public-wrapper-inflation` | 118 |
| `V0/syntactic-vacuity` | 106 |
| `V4/bridge-infrastructure-promoted` | 5 |

## Top Vacuity Suspicion (derived ranking)

| Rank | Declaration | Suspicion | Confidence | Key Factors |
|------|---------|----------:|-----------:|-------------|
| 1 | `InfoGeometry.Geometry.fenchelYoung_along_fderiv_of_concrete` | 0.7900 | 0.8030 | `shape.exact-forward`, `structure.low-public-fan-in`, `structure.low-descendant-mass` |
| 2 | `InfoGeometry.Canonical.Attention.polarizedSinkhornFinNonempty` | 0.7800 | 0.7999 | `shape.rfl-like`, `structure.low-descendant-mass`, `structure.low-public-fan-in` |
| 3 | `InfoGeometry.Canonical.PhaseSpaceConformalKKTBridge.toDoubledCopyRho_comp_phaseRotation_eq_KKT_dilationOperator` | 0.7700 | 0.8095 | `shape.exact-forward`, `structure.low-public-fan-in`, `structure.proof-only-reuse` |
| 4 | `InfoGeometry.Canonical.Attention.finNonempty` | 0.7500 | 0.8157 | `shape.rfl-like`, `structure.low-descendant-mass`, `structure.proof-only-reuse` |
| 5 | `InfoGeometry.Canonical.IB.pmf_normalize_eq_of_scale` | 0.7500 | 0.8157 | `shape.rfl-like`, `structure.low-descendant-mass`, `structure.proof-only-reuse` |
| 6 | `InfoGeometry.Canonical.KKTNoetherCharges.noether_charge_of_supercharge_split` | 0.7500 | 0.8157 | `shape.rfl-like`, `structure.low-descendant-mass`, `structure.proof-only-reuse` |
| 7 | `InfoGeometry.Quantum.KitaevChain.zero_exists_of_opposite_sign_symm` | 0.7500 | 0.8096 | `shape.exact-forward`, `structure.low-public-fan-in`, `structure.low-descendant-mass` |
| 8 | `InfoGeometry.Math.Convexity.neg_log_jensen_sum` | 0.7300 | 0.8259 | `shape.exact-forward`, `structure.low-public-fan-in`, `structure.low-descendant-mass` |
| 9 | `InfoGeometry.Twistor.Incidence.det_zero_of_annihilates_nonzero` | 0.7200 | 0.7925 | `shape.rfl-like`, `structure.low-descendant-mass`, `structure.low-public-fan-in` |
| 10 | `InfoGeometry.Canonical.WedgeBoostModularBridge.modularTime_roundtrip` | 0.7200 | 0.8094 | `shape.exact-forward`, `structure.low-public-fan-in`, `structure.shallow-depth` |
| 11 | `InfoGeometry.ExponentialFamily.Bernoulli.deriv_logPartition` | 0.7200 | 0.7849 | `shape.rfl-like`, `structure.low-public-fan-in`, `structure.low-descendant-mass` |
| 12 | `InfoGeometry.measurable_potential` | 0.7200 | 0.7849 | `shape.rfl-like`, `structure.low-public-fan-in`, `structure.low-descendant-mass` |
| 13 | `InfoGeometry.Geometry.legendre_involution_of_inverse_maps` | 0.7100 | 0.7941 | `shape.rfl-like`, `structure.low-descendant-mass`, `structure.low-public-fan-in` |
| 14 | `InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightPhaseAxis_eq_dilationOperator` | 0.7100 | 0.8096 | `shape.exact-forward`, `structure.low-public-fan-in`, `structure.shallow-depth` |
| 15 | `InfoGeometry.LLM.KMSSoftmaxBridge.kmsLogPartition_eq_logSumExpRouter` | 0.7100 | 0.8096 | `shape.exact-forward`, `structure.low-public-fan-in`, `structure.shallow-depth` |
| 16 | `InfoGeometry.Measure.DiscreteRN.rnDeriv_pmf_eq_div` | 0.7000 | 0.8191 | `shape.exact-forward`, `structure.proof-only-reuse`, `structure.low-public-fan-in` |
| 17 | `InfoGeometry.Convex.OneD.bregmanDiv_three_point` | 0.7000 | 0.8189 | `shape.exact-forward`, `structure.low-public-fan-in`, `structure.low-descendant-mass` |
| 18 | `InfoGeometry.Math.Convexity.kl_convexity_finite` | 0.7000 | 0.8189 | `shape.exact-forward`, `structure.low-public-fan-in`, `structure.low-descendant-mass` |
| 19 | `InfoGeometry.Measure.RadonNikodymNormalForms.rnDeriv_singleton_eq_mass_ratio` | 0.7000 | 0.8189 | `shape.exact-forward`, `structure.low-public-fan-in`, `structure.low-descendant-mass` |
| 20 | `InfoGeometry.Projective.logSumInequality` | 0.7000 | 0.8189 | `shape.exact-forward`, `structure.low-public-fan-in`, `structure.low-descendant-mass` |

## Structural Metrics (top 20 by transitive reverse reach)

| Declaration | Reverse Reach | Descendant Mass | Depth | SCC Role | Public Fan-In | Proof-Only Reuse |
|---------|--------------:|----------------:|------:|----------|---------------:|-----------------:|
| `InfoGeometry.Krein.instL2Complete` | 1846 | 0 | 25 | `acyclic` | 812 | 163 |
| `InfoGeometry.Krein.DoubledSpace.ext` | 1279 | 1 | 23 | `acyclic` | 0 | 159 |
| `InfoGeometry.Canonical.CertifiedInverseKernel.toInverseKernel` | 998 | 2 | 18 | `acyclic` | 103 | 35 |
| `InfoGeometry.Canonical.CertifiedInverseKernel.toInverseKernel'` | 951 | 3 | 17 | `acyclic` | 5 | 52 |
| `InfoGeometry.PositiveMeasure.pos` | 531 | 2 | 26 | `acyclic` | 0 | 24 |
| `InfoGeometry.Canonical.CertifiedInverseKernel.spectralProjector` | 489 | 8 | 16 | `acyclic` | 110 | 45 |
| `InfoGeometry.Projective.positiveMeasureToEuclidean_apply` | 463 | 3 | 26 | `acyclic` | 0 | 2 |
| `InfoGeometry.Projective.positiveMeasureToEuclidean_ne_zero` | 462 | 5 | 25 | `acyclic` | 0 | 4 |
| `InfoGeometry.PositiveMeasure.ext` | 461 | 6 | 22 | `acyclic` | 0 | 8 |
| `InfoGeometry.Projective.positiveMeasureToEuclidean_scale` | 460 | 5 | 24 | `acyclic` | 0 | 1 |
| `InfoGeometry.Projective.positiveMeasureToConeInteriorRay_sameRay` | 459 | 17 | 23 | `acyclic` | 0 | 1 |
| `InfoGeometry.Projective.projectiveClassToConeInteriorStateSpace_injective` | 452 | 25 | 21 | `acyclic` | 0 | 1 |
| `InfoGeometry.Projective.projectiveClassToConeInteriorStateSpace_surjective` | 452 | 22 | 21 | `acyclic` | 0 | 1 |
| `InfoGeometry.Projective.projectiveClassToConeInteriorStateSpace_bijective` | 451 | 28 | 20 | `acyclic` | 0 | 1 |
| `InfoGeometry.Krein.complex_i_apply` | 448 | 6 | 16 | `acyclic` | 0 | 130 |
| `InfoGeometry.Canonical.CertifiedInverseKernel.chiralAnomaly` | 423 | 12 | 12 | `acyclic` | 31 | 16 |
| `InfoGeometry.Krein.spectral_epsilon_involution` | 333 | 4 | 13 | `acyclic` | 1 | 13 |
| `InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.toConformalInference` | 332 | 2 | 18 | `acyclic` | 137 | 14 |
| `InfoGeometry.Canonical.CertifiedInverseKernel.metricProjector` | 329 | 8 | 15 | `acyclic` | 31 | 19 |
| `InfoGeometry.Canonical.CertifiedInverseKernel.rightChiralAnomaly` | 309 | 12 | 12 | `acyclic` | 20 | 14 |

## Errors (require action)

### `lean/InfoGeometry/Canonical/AttentionDiracBridge.lean`

- **`InfoGeometry.Canonical.AttentionDiracBridge.attentionHead_eq_of_matchForm_eq_diracPairing`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AttentionDiracBridge.attentionParams_eq_of_matchForm_eq_diracPairing`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AttentionDiracBridge.attentionWeights_eq_of_matchForm_eq_diracPairing`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AttentionDiracBridge.diracAttentionWeights_sum_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.AttentionDiracBridge.interactionEnergy_eq_of_matchForm_eq_diracPairing`** — `V2/dead-public-theorem`
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

### `lean/InfoGeometry/Canonical/BogoliubovPolarizationBridge.lean`

- **`InfoGeometry.Canonical.BogoliubovPolarizationBridge.bogoliubovPolarizationBridge_of_strictSymmetry`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.BogoliubovPolarizationBridge.car_realization_of_strictSymmetryBogoliubov`** — `V2/dead-public-theorem`
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

### `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean`

- **`InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.exists_zeroMode_and_nontrivial_regularization_pair_of_dim_mismatch`** — `V2/dead-public-theorem`
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

### `lean/InfoGeometry/Canonical/CentralChargeKKTParityBridge.lean`

- **`InfoGeometry.Canonical.CentralChargeKKTParityBridge.operatorialCentralChargeParity_eq_transport_slice`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.CentralChargeKKTParityBridge.quasilatticeAnalyticalIndexParity_transport_invariant`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ChiralDefectIndexBridge.lean`

- **`InfoGeometry.Canonical.ChiralDefectIndexBridge.transportedDefectBlockMinus_eq_dirac_comp_gradeProjMinus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ChiralDefectIndexBridge.transportedDefectBlockPlus_eq_dirac_comp_gradeProjPlus`** — `V2/dead-public-theorem`
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

### `lean/InfoGeometry/Canonical/ChiralHodgeIndexBridge.lean`

- **`InfoGeometry.Canonical.ChiralHodgeIndexBridge.rootDiracOddLane_analyticalIndex_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ChiralHodgeIndexBridge.root_chiralProjectorMinus_eq_spectralChiralMinusProjector`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ChiralHodgeIndexBridge.root_chiralProjectorPlus_eq_spectralChiralPlusProjector`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ChiralHodgeLichnerowiczBridge.lean`

- **`InfoGeometry.Canonical.ChiralHodgeLichnerowiczBridge.root_supercharge_lichnerowicz_minus_sector`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ChiralHodgeLichnerowiczBridge.root_supercharge_lichnerowicz_plus_sector`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/CliffordBridge.lean`

- **`InfoGeometry.Canonical.CliffordBridge.splitBilinear_eq_gaugeBilinear`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.CliffordBridge.B_agrees_with_Gauge_bilinear`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.CliffordBridge.splitQuadratic_eq_gaugeQuadratic`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.CliffordBridge.q_agrees_with_Gauge_quad`
  - Tags: `dead-candidate`, `wrapper-candidate`

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

### `lean/InfoGeometry/Canonical/DiagonalMetricModularBridge.lean`

- **`InfoGeometry.Canonical.DiagonalMetricModularBridge.countDiagonalHessianGeometryOfRelativeCountDensitySumBound_metricOp_eq_countModularHamiltonian`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DiagonalMetricModularBridge.countDiagonalHessianGeometryOfRelativeCountDensitySumBound_metricOp_eq_relativeTomitaTakesakiOp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DiagonalMetricModularBridge.spectral_dirac_sq_apply_eq_relativeModularHamiltonian_smul_of_isDiagonalRelativeCountMetricSlice`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DiagonalMetricModularBridge.spectral_dirac_sq_eq_countModularHamiltonian_of_isDiagonalRelativeCountMetricSlice`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/DrazinCentralChargeBridge.lean`

- **`InfoGeometry.Canonical.DrazinCentralChargeBridge.DrazinLane.exists_internal_split_with_intrinsic_nonScalar_shadow_and_witness`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DrazinCentralChargeBridge.DrazinLane.operatorialCentralScalar_eq_transport_slice`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DrazinCentralChargeBridge.instIsScalarTowerRealContinuousLinearMapIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DrazinCentralChargeBridge.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DrazinCentralChargeBridge.instSMulCommClassRealContinuousLinearMapIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/DrazinExistenceBridge.lean`

- **`InfoGeometry.Canonical.DrazinExistenceBridge.singular_isDrazinInverse_of_canonical`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/DrazinFredholmBridge.lean`

- **`InfoGeometry.Canonical.DrazinFredholmBridge.DefectChiralFredholmSurface.minusFinite`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DrazinFredholmBridge.DefectChiralFredholmSurface.plusFinite`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DrazinFredholmBridge.DrazinDefectFredholmPackage.defectCommMinusCompact`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DrazinFredholmBridge.DrazinDefectFredholmPackage.defectCommPlusCompact`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DrazinFredholmBridge.DrazinDefectFredholmPackage.defectCompact`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DrazinFredholmBridge.DrazinDefectFredholmPackage.defectSurface`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DrazinFredholmBridge.defectKernelDimMismatch_of_defectChiralIndex_ne_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/DrazinModularSingularityBridge.lean`

- **`InfoGeometry.Canonical.DrazinModularSingularityBridge.canonicalDefectCentral_singularity_package`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DrazinModularSingularityBridge.canonicalKineticPart_singularity_package`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DrazinModularSingularityBridge.defectProjectionObstruction_eq_zero_iff_commute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DrazinModularSingularityBridge.hD_fixed_under_modularFlow_of_commute_theta`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DrazinModularSingularityBridge.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DrazinModularSingularityBridge.instIsScalarTowerRealContinuousLinearMapIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DrazinModularSingularityBridge.instSMulCommClassRealContinuousLinearMapIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DrazinModularSingularityBridge.modularAdjointFlow_canonicalDefectCentral_eq_self_of_commute_generator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DrazinModularSingularityBridge.modularAdjointFlow_canonicalKineticPart_eq_self_of_commute_generator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DrazinModularSingularityBridge.modularAdjointFlow_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DrazinModularSingularityBridge.qD_preserved_under_modularFlow_of_commute_theta`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/DrazinSpectralBridge.lean`

- **`InfoGeometry.Canonical.DrazinSpectralBridge.DrazinInfiniteAssumptions_of_zeroIsolatedInSpectrum_classical`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DrazinSpectralBridge.DrazinInfiniteAssumptions_of_zeroIsolatedInSpectrum_finite_ascent_descent`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DrazinSpectralBridge.DrazinInfiniteAssumptions_of_zeroIsolatedInSpectrum_generalized`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DrazinSpectralBridge.DrazinInfiniteAssumptions_of_zeroIsolatedInSpectrum_zero_isolated`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.DrazinSpectralBridge.HasFiniteAscentDescentAtZero_of_zeroIsolatedInSpectrum_eq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/DrazinSpectralProjectorBridge.lean`

- **`InfoGeometry.Canonical.DrazinSpectralProjectorBridge.exists_drazin_projection_idempotent_of_zeroIsolatedInSpectrum_package`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/FisherVolumeBridge.lean`

- **`InfoGeometry.Canonical.FisherVolumeBridge.action_hessian_eq_fisher`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.FisherVolumeBridge.dynamic_rotation_preserves_hessian`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.FisherVolumeBridge.metric_to_phase_readout_bridge`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.FisherVolumeBridge.metric_to_phase_readout_bridge_comp_complex_i`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.FisherVolumeBridge.operatorial_uncertainty_area_law`** — `V2/dead-public-theorem`
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

### `lean/InfoGeometry/Canonical/HestenesKramersBridge.lean`

- **`InfoGeometry.Canonical.HestenesKramersBridge.inner_first_second_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.HestenesKramersBridge.kreinInner_phasePartner_phasePartner`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.HestenesKramersBridge.phasePartner_ne_self_of_ne_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/IBFrozenModularBridge.lean`

- **`InfoGeometry.Canonical.IB.ibBlahutArimotoStepFrozen_scalarModularPotential_sub_logPartitionFrozen_eq_betaKL`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/IBGaugeBridge.lean`

- **`InfoGeometry.Canonical.IBGaugeBridge.IBGibbsMeasure_shift_eq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IBGaugeBridge.ibProjectiveState_eq_of_shift`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.IBGaugeBridge.ibProjectiveState_normalize_eq_IBGibbs`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/InformationalLichnerowiczBottBridge.lean`

- **`InfoGeometry.Canonical.InformationalLichnerowiczBottBridge.cl11_bottDirac_sq_eq_zero_of_operatorialTransport`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/JaynesRNModularBridge.lean`

- **`InfoGeometry.Canonical.JaynesRNMaxEnt.neg_log_rnDeriv_gibbsMeasure_toReal_eq_neg_potential_add_logPartition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.JaynesRNMaxEnt.potential_eq_log_rnDeriv_gibbsMeasure_toReal_add_logPartition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.JaynesRNMaxEnt.scalarModularPotential_exp_potential_div_partition`** — `V2/dead-public-theorem`
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

### `lean/InfoGeometry/Canonical/KramersSuperchargeBridge.lean`

- **`InfoGeometry.Canonical.KramersSuperchargeBridge.hD_eq_hK_add_zD`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KramersSuperchargeBridge.hD_is_even`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KramersSuperchargeBridge.kramersPair_phasePartner_bridge`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KramersSuperchargeBridge.kramers_conjugated_qD_is_odd_of_commute_GammaS`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KramersSuperchargeBridge.majorana_closed_HD_of_commute_chi`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KramersSuperchargeBridge.majorana_closed_HK_and_ZD_of_commute_chi_and_Q0`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KramersSuperchargeBridge.majorana_closed_QD_of_commute_chi`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KramersSuperchargeBridge.majorana_closed_chiL_of_commute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.KramersSuperchargeBridge.majorana_closed_chiR_of_commute`** — `V2/dead-public-theorem`
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

### `lean/InfoGeometry/Canonical/LogSpineBridge.lean`

- **`InfoGeometry.Canonical.LogSpine.jordan_logdet_eq_zeta_determinant`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.LogSpine.kahler_spine_entropy_identity`** — `V2/dead-public-theorem`
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

### `lean/InfoGeometry/Canonical/ModularKLDivergenceBridge.lean`

- **`InfoGeometry.Canonical.ModularKLDivergenceBridge.generalizedKL_eq_klLike_add_massSlack`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularKLDivergenceBridge.generalizedKL_scale_shape_mass_term_pos_of_mass_ne`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularKLDivergenceBridge.generalizedKL_scale_shape_split_with_nonneg`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularKLDivergenceBridge.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularKLDivergenceBridge.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularKLDivergenceBridge.positiveRay_logGenerator_eq_neg_relativeLogDensity`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularKLDivergenceBridge.positiveRay_logGenerator_eq_relativeModularPotential_ae`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ModularKramersBridge.lean`

- **`InfoGeometry.Canonical.ModularKramersBridge.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularKramersBridge.instIsScalarTowerRealContinuousLinearMapIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularKramersBridge.instSMulCommClassRealContinuousLinearMapIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularKramersBridge.kramers_preserves_modularConjugation_fixed_of_commute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularKramersBridge.majoranaFix_preserved_under_modularFlow_of_commute_C`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularKramersBridge.modularConjugation_equivariant_kramersPair_of_commute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularKramersBridge.phaseAxisK_commutes_modularFlow_of_IsPhaseLinear`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularKramersBridge.theta_commutes_modularFlow_of_commute_generator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularKramersBridge.theta_preserves_modular_fixedSector_of_commute_flow`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ModularSourceBridge.lean`

- **`InfoGeometry.Canonical.ModularSourceBridge.sourcedModularGenerator_boundary_excitation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularSourceBridge.sourcedModularGenerator_bulk_invariant`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ModularSpectralConjugationBridge.lean`

- **`InfoGeometry.Canonical.ModularSpectralConjugationBridge.Compatibility.P_D_mul_activeModularConjugation_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularSpectralConjugationBridge.Compatibility.activeModularConjugation_eq_modular_j_mul_spectralProjector_of_modularSign`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularSpectralConjugationBridge.Compatibility.activeModularConjugation_mul_P_D_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularSpectralConjugationBridge.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularSpectralConjugationBridge.instIsScalarTowerRealContinuousLinearMapIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularSpectralConjugationBridge.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularSpectralConjugationBridge.instSMulCommClassRealContinuousLinearMapIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/ModularSpectralWedgeBridge.lean`

- **`InfoGeometry.Canonical.ModularSpectralWedgeBridge.IsCompatibleWedge.P_D_mul_owned_epsilon_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularSpectralWedgeBridge.IsCompatibleWedge.owned_epsilon_mul_P_D_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularSpectralWedgeBridge.WedgeCalibrated.flow_commutes_pzero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.ModularSpectralWedgeBridge.WedgeCalibrated.flow_commutes_wedgeSign`** — `V2/dead-public-theorem`
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

### `lean/InfoGeometry/Canonical/ModularWeldBridge.lean`

- **`InfoGeometry.Canonical.ModularWeldBridge.relativeModularOperator_eq_exp_relativeLogDensityOperator`** — `V2/dead-public-theorem`
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

### `lean/InfoGeometry/Canonical/NavierStokesBridge.lean`

- **`InfoGeometry.Canonical.FluidState.density_stationary`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.adjoint_vorticity_eq_neg`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.anomalyFluidStateWithDensity_rho`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.anomalyFluidStateWithDensity_u`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.anomalyFluidState_momentumResidual_eq_zero_of_regularization_canonical`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.anomalyFluidState_momentumResidual_eq_zero_of_regularization_global_drazin`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.anomalyFluidState_momentumResidual_eq_zero_of_regularization_of_finiteDimensional`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.anomalyFluidState_momentumResidual_eq_zero_of_skew`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.anomalyMomentumResidual_eq_zero_of_regularization_canonical`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.anomalyMomentumResidual_eq_zero_of_regularization_global_drazin`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.anomalyMomentumResidual_eq_zero_of_regularization_of_finiteDimensional`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.anomalySkew_of_regularization_canonical`** — `V2/dead-public-theorem`
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

### `lean/InfoGeometry/Canonical/OperatorAlgebraKKBridge.lean`

- **`InfoGeometry.Canonical.OperatorAlgebraBridge.kk_supercomm_compact_of_even_rep`** — `V2/dead-public-theorem`
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
- **`InfoGeometry.Canonical.PolarizedMadelungBridge.PolarizedDoubledAmplitude.modular_j_phaseOrbit_eq_reverse_complex_i`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PolarizedMadelungBridge.PolarizedDoubledAmplitude.phaseOrbit_eq_complex_iOrbit`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PolarizedMadelungBridge.PolarizedDoubledAmplitude.phaseOrbit_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PolarizedMadelungBridge.PolarizedDoubledAmplitude.sheet_decomposition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PolarizedMadelungBridge.PolarizedDoubledAmplitude.ψminus_mem_minusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PolarizedMadelungBridge.PolarizedDoubledAmplitude.ψplus_mem_plusSheet`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PolarizedMadelungBridge.StateGeneratorField.statePhaseReadout_eq_metric_comp_complex_i`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PolarizedMadelungBridge.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PolarizedMadelungBridge.kreinExpectation_minusPoint`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.PolarizedMadelungBridge.kreinExpectation_plusPoint`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/PositiveRayProjectiveBridge.lean`

- **`InfoGeometry.Canonical.PositiveRayProjectiveBridge.positiveRayToProjectiveState_normalize_eq`** — `V2/dead-public-theorem`
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
- **`InfoGeometry.Canonical.QuantumLieAlgebroidRosetta.paper_phaseReadout_eq_metric_comp_complex_i`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.QuantumLieAlgebroidRosetta.paper_phaseReadout_eq_metric_comp_internalPhaseAxis`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.QuantumLieAlgebroidRosetta.paper_schrodingerCurrent_eq_probe_anchor`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RNDeterminantConnesChainBridge.lean`

- **`InfoGeometry.Canonical.RNDeterminantConnesChainBridge.jacobianDeterminant_chain`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RNDeterminantConnesChainBridge.relativeDensity_state_chain`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RNDeterminantConnesChainBridge.relativeModularVolumeShadow_state_chain`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RNDeterminantConnesChainBridge.rn_state_chain`** — `V2/dead-public-theorem`
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

### `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean`

- **`InfoGeometry.Canonical.RelativeModularProjectiveBridge.RestrictedRelativeModularData.local_projectiveLogGenerator_eq_pullback_ambient_add_shift`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularProjectiveBridge.RestrictedRelativeModularData.local_projectiveLogGenerator_eq_pullback_ambient_add_shift_ae`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.RelativeModularProjectiveBridge.RestrictedRelativeModularData.projectiveCountHamiltonianProfile_eq_pullback_ambient_add_shift`** — `V2/dead-public-theorem`
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

### `lean/InfoGeometry/Canonical/RosettaScaleTransport.lean`

- **`InfoGeometry.Canonical.Rosetta.isJordanKKTGeometry_of_weylScaleTransportShadow`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Rosetta.kk_analyticalIndex_eq_of_weylScaleTransport`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Rosetta.weylScaleTransportScalarShadow_eq_jordanBregman_of_isJordanKKTGeometry`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/RosettaSourceBridge.lean`

- **`InfoGeometry.Canonical.Rosetta.complex_i_toLinearMap_eq_realMajoranaKAxis`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.Rosetta.instCompleteSpaceVCl11DoubledCore`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/SouriauFlowCliffordBridge.lean`

- **`InfoGeometry.Canonical.SouriauFlowCliffordBridge.deriv_apply_operatorialGibbsWeight_zero_eq_neg_expectation_souriau`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SouriauFlowCliffordBridge.sourceSink_souriau_defect_split_of_connection_eq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SouriauFlowCliffordBridge.souriau_comp_eq_jordan_plus_lie`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SouriauFlowCliffordBridge.souriau_fockAnticommutator_eq_two_smul_jordanProduct`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SouriauFlowCliffordBridge.souriau_fockCommutator_eq_two_smul_lieProduct`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SouriauFlowCliffordBridge.souriau_stateQGTPhaseReadout_eq_metric_comp_complex_i`** — `V2/dead-public-theorem`
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
- **`InfoGeometry.Canonical.SpinorModularBridge.boundary_active_on_nonzero_kernel_iff_kernel_separation`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SpinorModularBridge.coriolisVorticity_ne_zero_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SpinorModularBridge.coriolisVorticity_ne_zero_of_operatorialCentralCharge_ne_zero_of_kernelSeparation_of_identifiedTransportedPolarization`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SpinorModularBridge.curvature_concentrated_on_dangling_modes`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SpinorModularBridge.horizon_is_scale_invariant`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/SplitCliffordHeadLift.lean`

- **`InfoGeometry.Canonical.SplitCliffordHeadLift.headEpsTensor_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/SplitCliffordTensorBridge.lean`

- **`InfoGeometry.Canonical.SplitCliffordTensorBridge.doubledHeadAtom_feeds_first_tensorStep_J`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SplitCliffordTensorBridge.doubledHeadAtom_feeds_first_tensorStep_K`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SplitCliffordTensorBridge.doubledHeadAtom_supergradedLiePackage_root`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.SplitCliffordTensorBridge.doubledHeadAtom_supergradedLiePackage`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.SplitCliffordTensorBridge.splitCl44_tailFactor`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/SplitCliffordThermalBridge.lean`

- **`InfoGeometry.Canonical.SplitCliffordThermalBridge.splitCliffordThermalBridge_of_strictSymmetry`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SplitCliffordThermalBridge.transportedThermalFlow_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SplitCliffordThermalBridge.transportedThermalGenerator_eq_transportDirac_of_zeroChemicalPotential`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/SuperchargeCARCCRBridge.lean`

- **`InfoGeometry.Canonical.SuperchargeCARCCRBridge.carBracket_swap`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeCARCCRBridge.ccrBracket_swap`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeCARCCRBridge.complex_i_maps_minus_to_plus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeCARCCRBridge.complex_i_maps_plus_to_minus`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeCARCCRBridge.complex_i_sq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeCARCCRBridge.cptSuperchargeOp_eq_dilationOperator`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.Canonical.TomitaTakesaki.modularCPTSupercharge_Q_eq_dilationOperator`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.Canonical.SuperchargeCARCCRBridge.cptSuperchargeOp_eq_modular_j_comp_spectral_epsilon`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeCARCCRBridge.fockEndomorphism_eq_doubledEnd`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeCARCCRBridge.modularSuperchargeOp_eq_spectral_epsilon`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeCARCCRBridge.modular_j_spectral_epsilon_car_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeCARCCRBridge.modular_j_spectral_epsilon_ccr_eq_two_complex_i`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeCARCCRBridge.paritySuperchargeOp_eq_modular_j`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/SuperchargeEinsteinSourceBridge.lean`

- **`InfoGeometry.Canonical.SuperchargeEinsteinSourceBridge.SuperchargeBoundaryCarrierCompatibility.metricProj_eq_transportedProj`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeEinsteinSourceBridge.SuperchargeBoundaryCarrierCompatibility.mismatch_forces_projector_noncommute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeEinsteinSourceBridge.SuperchargeBoundaryCarrierCompatibility.spectralProj_eq_superchargeProj`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeEinsteinSourceBridge.SuperchargeProjectorCompatibility.metricProj_eq_transportedProj`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeEinsteinSourceBridge.SuperchargeProjectorCompatibility.spectralProj_eq_superchargeProj`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeEinsteinSourceBridge.chiralScale_ne_zero_and_einsteinEquation_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization_on_boundaryCarrier`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeEinsteinSourceBridge.chiralScale_ne_zero_and_einsteinEquation_of_operatorialCentralCharge_ne_zero_of_mismatch_forces_projector_noncommute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeEinsteinSourceBridge.chiralScale_ne_zero_and_einsteinEquation_of_quasilatticeAnalyticalIndex_ne_zero_of_identifiedTransportedPolarization_on_boundaryCarrier`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeEinsteinSourceBridge.chiralScale_ne_zero_and_einsteinEquation_of_quasilatticeAnalyticalIndex_ne_zero_of_mismatch_forces_projector_noncommute`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeEinsteinSourceBridge.conformal_projector_noncommute_of_boundary_projector_noncommute_of_alignment`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeEinsteinSourceBridge.einsteinEquation_of_transportedIndexMismatch_source`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeEinsteinSourceBridge.projectorObstruction_ne_zero_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization_on_boundaryCarrier`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeEinsteinSourceBridge.projectorObstruction_ne_zero_of_quasilatticeAnalyticalIndex_ne_zero_of_compat`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeEinsteinSourceBridge.projectorObstruction_ne_zero_of_quasilatticeAnalyticalIndex_ne_zero_of_identifiedTransportedPolarization_on_boundaryCarrier`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeEinsteinSourceBridge.superchargeBoundaryCarrierCompatibility_of_identifiedTransportedPolarization`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeEinsteinSourceBridge.superchargeBoundaryCarrierCompatibility_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeEinsteinSourceBridge.superchargeBoundaryCarrierCompatibility_of_quasilatticeAnalyticalIndex_ne_zero_of_identifiedTransportedPolarization`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeEinsteinSourceBridge.superchargeProjectorCompatibility_of_boundaryScale_ne_zero_of_mismatch`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/SuperchargeGapBridge.lean`

- **`InfoGeometry.Canonical.SuperchargeGapBridge.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeGapBridge.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeGapBridge.transportedParityModularGapSeed_eq_split_generator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeGapBridge.transportedParityModularGapSeed_eq_zero_of_commute_modularJ`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeGapBridge.transportedParityModularGap_zero_eq_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/SuperchargeGapHessianBridge.lean`

- **`InfoGeometry.Canonical.SuperchargeGapHessianBridge.deriv2_transportedParitySupercharge_at_zero_eq_metricPart_add_half_curvaturePart_cpt_lane`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeGapHessianBridge.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeGapHessianBridge.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeGapHessianBridge.transportedParityModularGapSeed_eq_cpt_lane_transportSeed`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeGapHessianBridge.transported_gapSeed_hessian_curvature_root_package`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeGapHessianBridge.transported_gapSeed_hessian_curvature_with_oscillator_spine`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/SuperchargeRoleBridge.lean`

- **`InfoGeometry.Canonical.SuperchargeRoleBridge.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeRoleBridge.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeRoleBridge.transportedModularSupercharge_zero_eq_spectral_epsilon`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeRoleBridge.transportedParityModularGapSeed_eq_phaseAntilinearCAR_root_of_commute_phaseLinearPart`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeRoleBridge.transportedParitySupercharge_zero_eq_modular_j`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/SuperchargeTransportBridge.lean`

- **`InfoGeometry.Canonical.SuperchargeTransportBridge.deriv2_transportedParitySupercharge_at_zero_eq_operatorInformationMetricPart`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeTransportBridge.deriv_transportedModularSupercharge_at_zero_eq_phaseAntilinear_of_commute_phaseLinearPart`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeTransportBridge.deriv_transportedParitySupercharge_at_zero_eq_phaseAntilinear_of_commute_phaseLinearPart`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.SuperchargeTransportBridge.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/VortexReferenceGaugeBridge.lean`

- **`InfoGeometry.Canonical.VortexReferenceGaugeBridge.comparisonPhaseReadout_sinkVortexSeed_eq_of_sinkSectorDegeneracy`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.VortexReferenceGaugeBridge.comparisonPhaseReadout_sourceVortexSeed_eq_of_sourceSectorDegeneracy`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.VortexReferenceGaugeBridge.functionalShift_eq_of_sinkSectorDegeneracy`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.VortexReferenceGaugeBridge.functionalShift_eq_of_sourceSectorDegeneracy`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.VortexReferenceGaugeBridge.twoStateGap_eq_of_sinkSectorDegeneracy`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.VortexReferenceGaugeBridge.twoStateGap_eq_of_sourceSectorDegeneracy`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/WedgeBoostModularBridge.lean`

- **`InfoGeometry.Canonical.WedgeBoostModularBridge.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WedgeBoostModularBridge.instIsScalarTowerRealContinuousLinearMapIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WedgeBoostModularBridge.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WedgeBoostModularBridge.instSMulCommClassRealContinuousLinearMapIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WedgeBoostModularBridge.modularTimeOfWedgeBoost_agrees_with_standardForm`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.WedgeBoostModularBridge.modularTime_roundtrip`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.RealTomitaCore.modularTimeOfWedgeBoost_wedgeBoostParameter`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Canonical.WedgeBoostModularBridge.wedgeBoostParameter_agrees_with_standardForm`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Canonical/WeightedWeylNormalizationBridge.lean`

- **`InfoGeometry.Canonical.WeightedWeylNormalizationBridge.densityWeightLiftedReadout_pair_eq_zeroWeight_add_weighted_phaseAxisReadout`** — `V2/dead-public-theorem`
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

### `lean/InfoGeometry/Canonical/YangMillsFiniteBridge.lean`

- **`InfoGeometry.Canonical.YangMillsFinite.FiniteYangMillsBridge.existenceClaims_of_bridge`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.YangMillsFinite.FiniteYangMillsBridge.gamma_le_spectral_gap`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Canonical.YangMillsFinite.FiniteYangMillsBridge.obligations_of_expectationSeedFromLogDet`** — `V2/dead-public-theorem`
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

### `lean/InfoGeometry/Geometry/DualFlat.lean`

- **`InfoGeometry.Geometry.DualFlat.DualFlatStructure.h_convex`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.DualFlat.DualFlatStructure.h_diff`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.DualFlat.ProjectiveBridge.UnnormalizedMeasure.mass_pos`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.DualFlat.ProjectiveBridge.bayesian_update_pythagorean_bregman`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.DualFlat.ProjectiveBridge.projectiveDivergence_eq_kl`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.DualFlat.ProjectiveBridge.projectiveDivergence_eq_of_representative_eq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.DualFlat.divergence_self`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.HessianManifold.twiceDiff`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.HilbertHessian.twiceDiff`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.convex_iff_eGeodesicConvex`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Geometry.convexOn_univ_iff_eGeodesicConvex`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Geometry.divergenceVec_pythagorean`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.divergence_pythagorean`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.divergence_self`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.dualCoord_mGeodesic`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.eGeodesic_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.eGeodesic_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.mGeodesic_one`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.mGeodesic_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Geometry/KreinAsHessian.lean`

- **`InfoGeometry.Geometry.hasFDerivAt_krein_grad`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.hasFDerivAt_krein_potential`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.krein_form_self`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.krein_form_self_to_doubled_real`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Geometry.krein_form_to_doubled_real`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Geometry.krein_form_symm`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.krein_grad_eq_hessian_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.krein_hessian_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.krein_hessian_eq_spectral_epsilon`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.krein_hessian_sq`** — `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Krein.spectral_epsilon_involution`
  - Tags: `dead-candidate`, `wrapper-candidate`
- **`InfoGeometry.Geometry.krein_potential_to_doubled_real`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.two_mul_krein_potential`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Geometry/LegendreDuality.lean`

- **`InfoGeometry.Geometry.LegendreWellPosed.bddAbove`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.LegendreWellPosed.nonempty`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.dual_value_along_grad_of_fenchelYoung`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.fenchelGap_eq_zero_along_fderiv_of_concrete`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.fenchelGap_nonneg`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.fenchelGap_zero_along_grad_of_fenchelYoung`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.fenchelYoung_ineq`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.isFenchelMajorized_of_concrete`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Geometry.legendre_involution_of_inverse_maps`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`, `rfl-like`

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
- **`InfoGeometry.Krein.HilbertDoubled.ofDoubledContinuousLinearEquiv_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.HilbertDoubled.ofDoubledLIE_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.HilbertDoubled.ofLp_toLp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.HilbertDoubled.ofWithLp_val`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.HilbertDoubled.snd_ofWithLp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.HilbertDoubled.snd_toLp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.HilbertDoubled.toDoubledContinuousLinearEquiv_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.HilbertDoubled.toDoubledLIE_apply`** — `V2/dead-public-theorem`
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
- **`InfoGeometry.Krein.NeutralSpace.neutralJ_eq_J`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.NeutralSpace.neutralLift_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.NeutralSpace.ofWithLp_val`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.NeutralSpace.rotation45ToHilbertContinuousLinearEquiv_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Krein.NeutralSpace.rotation45ToHilbert_apply`** — `V2/dead-public-theorem`
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

### `lean/InfoGeometry/LLM/DiscreteRouterBayesRegularizationBridge.lean`

- **`InfoGeometry.LLM.bayesRouterUpdate_regularizedSignal_eq_coreSignal`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.LLM.bayesRouterUpdate_regularizedSignal_lambda_invariant`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/LLM/KMSSoftmaxBridge.lean`

- **`InfoGeometry.LLM.KMSSoftmaxBridge.beta_mul_routerFreeEnergy_eq_neg_kmsLogPartition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.LLM.KMSSoftmaxBridge.kmsEntropy_eq_beta_internal_plus_logPartition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.LLM.KMSSoftmaxBridge.kmsLogPartition_eq_logSumExpRouter`** — `V1/public-wrapper-inflation`
  - Forwards to: `InfoGeometry.LLM.RouterFreeEnergyBridge.routerMassieu_eq_logSumExpRouter`
  - Tags: `proof-infrastructure`, `wrapper-candidate`
- **`InfoGeometry.LLM.KMSSoftmaxBridge.routerFreeEnergyEps_eq_neg_eps_kmsLogPartition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.LLM.KMSSoftmaxBridge.softmaxWeight_eq_exp_routerLogit_div_partition`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.LLM.KMSSoftmaxBridge.softmaxWeight_eq_kmsWeight`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/LLM/PinCPTBridge.lean`

- **`InfoGeometry.LLM.PinCPTBridge.PinAction.odd_iff_anticommutator_zero`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/LLM/RouterFreeEnergyBridge.lean`

- **`InfoGeometry.LLM.RouterFreeEnergyBridge.routerScaledEntropicObjective_eq_scaledKL`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.LLM.RouterFreeEnergyBridge.routerScaledPotentialGap_eq_scaledBregman`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.LLM.RouterFreeEnergyBridge.routerScaledPotentialGap_eq_scaledBregman_swapped`
  - Tags: `dead-candidate`, `wrapper-candidate`

### `lean/InfoGeometry/LLM/ScalarThermoBridge.lean`

- **`InfoGeometry.LLM.ScalarThermoBridge.fenchelGap_nonneg_bridge`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.LLM.ScalarThermoBridge.logSumExpRouter_eq_analytic_logSumExp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.LLM.ScalarThermoBridge.logSumExpRouter_eq_convex_lse`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.LLM.ScalarThermoBridge.normalizedWeights_eq_analytic_logSumExpWeight`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.LLM.ScalarThermoBridge.switchMatrix_mem_rowStochastic_bridge`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Canonical.MoE.switchMatrix_mem_rowStochastic`
  - Tags: `dead-candidate`, `wrapper-candidate`

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

### `lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean`

- **`InfoGeometry.Quantum.GeometricQuantumTensor.berryTwoFormJEpsOfOperator_apply`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.berryTwoFormJEpsOfOperator_apply_eq_berryOfOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.berryTwoFormJEpsOfOperator_apply_root`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.berryTwoFormJEpsOfOperator_liftedEinsteinAnomalyOperator_eq_neg_liftedProjectorObstructionOperator_of_projectorAgreement`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.complex_i_star_eq_neg`** — `V1/public-wrapper-inflation`, `V2/dead-public-theorem`
  - Forwards to: `InfoGeometry.Quantum.GeometricQuantumTensor.modularComplexI_star_eq_neg`
  - Tags: `dead-candidate`, `wrapper-candidate`
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
- **`InfoGeometry.Quantum.GeometricQuantumTensor.inner_apply_spectral_epsilon_eq_kreinInner`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.inner_spectral_epsilon_apply_eq_kreinInner`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.isPhaseLinear_modularComplexI_comp_liftedEinsteinAnomalyOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.isSelfAdjoint_modularComplexI_comp_liftedEinsteinAnomalyOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator_complex_i_skew_of_commutesWith_complex_i`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.metricOfOperator_spectral_epsilon_comp_eq_kreinMetricOfOperator`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.modularVarianceSeed_eq_spectral_epsilon_comp`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.qgtOfOperator_modularVarianceSeed_realizes_modularVariance`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.qgtOfOperator_spectral_epsilon_comp_berry_eq_kreinQgtOfOperator_berry`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.GeometricQuantumTensor.qgtOfOperator_spectral_epsilon_comp_metric_eq_kreinQgtOfOperator_metric`** — `V2/dead-public-theorem`
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

### `lean/InfoGeometry/Quantum/RosettaSynthesis.lean`

- **`InfoGeometry.Quantum.RosettaSynthesis.instCompleteSpaceVCl11DoubledCore`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RosettaSynthesis.rosetta_anomaly_free_triality`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`
- **`InfoGeometry.Quantum.RosettaSynthesis.rosetta_source_tension_synthesis`** — `V2/dead-public-theorem`
  - Tags: `dead-candidate`

### `lean/InfoGeometry/Quantum/SplitTrialityFockBridge.lean`

- **`InfoGeometry.Quantum.SplitTrialityFockBridge.trialitySupercharge_square_eq_id_via_cliffordConcreteCAR`** — `V2/dead-public-theorem`
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

## Most-Affected Files (top 20)

| File | Violations |
|------|------------|
| `lean/InfoGeometry/Canonical/BerryConnection.lean` | 37 |
| `lean/InfoGeometry/Krein/HilbertBridge.lean` | 32 |
| `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean` | 31 |
| `lean/InfoGeometry/Quantum/HestenesKahler.lean` | 31 |
| `lean/InfoGeometry/Quantum/RealMajorana.lean` | 31 |
| `lean/InfoGeometry/Canonical/TransportLieDerivative.lean` | 28 |
| `lean/InfoGeometry/Core/SymmetricLieSpaces.lean` | 28 |
| `lean/InfoGeometry/Canonical/RicciMongeAmpere.lean` | 27 |
| `lean/InfoGeometry/MaxEnt/Jaynes.lean` | 27 |
| `lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean` | 26 |
| `lean/InfoGeometry/Canonical/SinkhornFoundation.lean` | 25 |
| `lean/InfoGeometry/Thermal/FiniteMatrix.lean` | 25 |
| `lean/InfoGeometry/Canonical/RelativeModularSingularization.lean` | 24 |
| `lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean` | 24 |
| `lean/InfoGeometry/Canonical/RestrictedSheetContinuous.lean` | 24 |
| `lean/InfoGeometry/Quantum/ModularAnomaly.lean` | 24 |
| `lean/InfoGeometry/Canonical/ModularSuperchargeClosure.lean` | 22 |
| `lean/InfoGeometry/Canonical/MongeAmpereDualSheetBridge.lean` | 22 |
| `lean/InfoGeometry/Canonical/StandardFormCore.lean` | 22 |
| `lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean` | 20 |
