# Repository Story From Full Lean Keyword Index

- generated: `2026-04-15T21:19:01+00:00`
- git head: `efee09366b90c535fce47f6a0c69b9148b12f508`
- indexed tracked Lean files: `850`
- selector profile: `methodology`
- characteristic terms selected: `24`

## Method

1. Full lexical index over all tracked `*.lean` files, sorted by frequency.
2. Characteristic-term selection by count × log(doc-frequency + 1), plus profile-term bias.
3. Deep search over declaration blocks (`theorem`, `lemma`, `axiom`) for each selected term.

## Characteristic Terms

| term | count | doc freq | score | declaration hits |
| --- | ---: | ---: | ---: | ---: |
| `modular` | 9350 | 230 | 50886.61 | 1157 |
| `spectral` | 5073 | 210 | 27149.98 | 772 |
| `depth` | 3100 | 237 | 25964.04 | 1103 |
| `transport` | 4634 | 236 | 25338.99 | 1136 |
| `relative` | 4435 | 145 | 22102.30 | 447 |
| `metric` | 4038 | 176 | 20901.29 | 730 |
| `generator` | 3477 | 191 | 18280.31 | 757 |
| `chiral` | 3633 | 141 | 18004.52 | 585 |
| `potential` | 3117 | 177 | 16151.62 | 464 |
| `kernel` | 2668 | 116 | 12705.48 | 523 |
| `inverse` | 2567 | 137 | 12648.26 | 566 |
| `measure` | 2717 | 93 | 12344.13 | 242 |
| `audit` | 97 | 14 | 12262.68 | 14 |
| `vacuity` | 83 | 22 | 12260.25 | 2 |
| `anomaly` | 2583 | 110 | 12164.72 | 376 |
| `representation` | 126 | 59 | 10515.89 | 18 |
| `projective` | 2213 | 114 | 10500.53 | 223 |
| `drazin` | 2323 | 89 | 10453.06 | 400 |
| `clifford` | 1993 | 157 | 10089.75 | 183 |
| `semantic` | 279 | 31 | 9966.94 | 29 |
| `morphism` | 316 | 24 | 9517.16 | 193 |
| `information` | 1766 | 192 | 9293.91 | 369 |
| `continuous` | 1772 | 177 | 9182.12 | 489 |
| `closure` | 692 | 93 | 9143.96 | 227 |

## Deep Declaration Search

### `modular`
- declaration matches: `1157` (theorem `1034`, lemma `123`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/auto_blueprints.lean` (986), `lean/InfoGeometry/Canonical/ModularSuperchargeClosure.lean` (527), `lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean` (484), `lean/InfoGeometry/Canonical/BogoliubovTransport.lean` (399)
- sample declarations:
  - `theorem isStateAlgebraicallyStationary_iff_generatorStationarity` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:110`
  - `theorem isStateAlgebraicallyStationary_iff_algebraicEinsteinBalance` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:123`
  - `theorem starCertifiedEinsteinAnomalyStationary_iff_projectorObstructionStationary_of_projectorAgreement` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:145`
  - `theorem phaseAxisResponse_eq_neg_KVariation` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:234`
  - `theorem KVariation_phaseAxisResponse_eq_neg_modularCurvature` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:247`
  - `theorem modularCurvatureExpectation_eq_zero_of_phaseResponseStationary` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:263`
  - `theorem chiralSliceIsoAlong_of_conjugacy` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:657`
  - `theorem chiralSliceIsoAlong_of_modularCliffordUnitTransport` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:723`

### `spectral`
- declaration matches: `772` (theorem `701`, lemma `71`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/auto_blueprints.lean` (458), `lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean` (329), `lean/InfoGeometry/Canonical/CartanDecomposition.lean` (286), `lean/InfoGeometry/Canonical/DrazinSupercharge.lean` (262)
- sample declarations:
  - `theorem einsteinHilbertAction_eq_neg_six_dual_pairing_sub_dual_of_compatible` — `lean/InfoGeometry/Canonical/ActionDuality.lean:39`
  - `theorem einsteinHilbertAction_and_zeroGap_of_compatible` — `lean/InfoGeometry/Canonical/ActionDuality.lean:58`
  - `theorem chiralSliceIsoAlong_of_const_finrank` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:294`
  - `theorem chiralNoZeroCrossingAlong_of_gap` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:438`
  - `theorem cl11GlobalGrading_apply_tmul` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:1049`
  - `theorem dilation_anomaly_jacobi_expansion` — `lean/InfoGeometry/Canonical/AnomalyDilationBridge.lean:39`
  - `theorem trace_dilation_eq_zero` — `lean/InfoGeometry/Canonical/AnomalyDilationBridge.lean:59`
  - `theorem anomaly_inflow_cancellation` — `lean/InfoGeometry/Canonical/AnomalyInflow.lean:62`

### `depth`
- declaration matches: `1103` (theorem `1096`, lemma `7`, axiom `0`)
- lexical hotspots: `lean/DAG/RepresentationDepthExport.lean` (137), `lean/DAG/ProcessFlowExport.lean` (105), `lean/InfoGeometry/Canonical/DrazinSupercharge.lean` (96), `lean/InfoGeometry/Canonical/ModularSuperchargeClosure.lean` (72)
- sample declarations:
  - `theorem isStateAlgebraicallyStationary_iff_generatorStationarity` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:110`
  - `theorem isStateAlgebraicallyStationary_iff_algebraicEinsteinBalance` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:123`
  - `theorem starCertifiedEinsteinAnomalyStationary_iff_projectorObstructionStationary_of_projectorAgreement` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:145`
  - `theorem operatorInformationFirstVariation_neg_left` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:181`
  - `theorem operatorInformationFirstVariation_neg_right` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:192`
  - `theorem isAlgebraicallyStationary_zero` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:203`
  - `theorem isStationaryAlong_of_commute` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:212`
  - `theorem isAlgebraicallyStationary_of_central` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:225`

### `transport`
- declaration matches: `1136` (theorem `1091`, lemma `45`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/auto_blueprints.lean` (434), `lean/InfoGeometry/Canonical/BogoliubovTransport.lean` (211), `lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean` (211), `lean/InfoGeometry/Canonical/ModularSuperchargeClosure.lean` (144)
- sample declarations:
  - `theorem grandCanonicalEulerStep_eq_of_vacuumSplit` — `lean/InfoGeometry/Canonical/AQFTOperatorEndpoints.lean:33`
  - `theorem isStateAlgebraicallyStationary_iff_generatorStationarity` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:110`
  - `theorem isStateAlgebraicallyStationary_iff_algebraicEinsteinBalance` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:123`
  - `theorem starCertifiedEinsteinAnomalyStationary_iff_projectorObstructionStationary_of_projectorAgreement` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:145`
  - `theorem operatorInformationFirstVariation_neg_left` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:181`
  - `theorem operatorInformationFirstVariation_neg_right` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:192`
  - `theorem isAlgebraicallyStationary_zero` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:203`
  - `theorem isStationaryAlong_of_commute` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:212`

### `relative`
- declaration matches: `447` (theorem `419`, lemma `28`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/auto_blueprints.lean` (495), `lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean` (467), `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean` (274), `lean/InfoGeometry/Canonical/RelativeModularOperator.lean` (264)
- sample declarations:
  - `theorem isStateAlgebraicallyStationary_iff_generatorStationarity` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:110`
  - `theorem topologicalBekensteinBound_of_connesCocycle_generatorLift_zero` — `lean/InfoGeometry/Canonical/BekensteinBound.lean:408`
  - `theorem cocycleGeneratorLift_of_casiniIncrementBridge` — `lean/InfoGeometry/Canonical/BekensteinBound.lean:456`
  - `theorem relEnt_drop_nonneg_of_casiniIncrementBridge` — `lean/InfoGeometry/Canonical/BekensteinBound.lean:476`
  - `theorem topologicalBekensteinBound_of_connesCocycle_casiniIncrement` — `lean/InfoGeometry/Canonical/BekensteinBound.lean:491`
  - `theorem topologicalBekensteinBound_of_tomitaConnesCocycle_casiniIncrement` — `lean/InfoGeometry/Canonical/BekensteinBound.lean:608`
  - `theorem topologicalBekensteinBound_of_tomitaFlowUnitConnesCocycle_casiniIncrement` — `lean/InfoGeometry/Canonical/BekensteinBound.lean:638`
  - `theorem KRotation_add` — `lean/InfoGeometry/Canonical/BerryConnection.lean:255`

### `metric`
- declaration matches: `730` (theorem `594`, lemma `136`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/auto_blueprints.lean` (335), `lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean` (245), `lean/InfoGeometry/Canonical/GeneralizedMetricCore.lean` (235), `lean/InfoGeometry/Clifford/PhaseSpaceGeneralizedMetric.lean` (173)
- sample declarations:
  - `lemma spinFactor_poly_identity` — `lean/InfoGeometry/Architecture/SpinFactor.lean:31`
  - `lemma symmetry_symmetry` — `lean/InfoGeometry/Architecture/SymmetricSpace.lean:21`
  - `lemma symmetry_self` — `lean/InfoGeometry/Architecture/SymmetricSpace.lean:28`
  - `lemma SymmetricPair.K_eq_fixedSubgroup` — `lean/InfoGeometry/Architecture/SymmetricSpace.lean:115`
  - `lemma cartanSymmetryOfInvolutiveMulAut_fixpoint` — `lean/InfoGeometry/Architecture/SymmetricSpace.lean:161`
  - `theorem sinkhornIterate_sinkhornKMSCapstone_of_closure` — `lean/InfoGeometry/Canonical/AnalyticalIndexCapstone.lean:51`
  - `lemma FullThermoGeoIndexCapstone.geometricAlgebraicState` — `lean/InfoGeometry/Canonical/AnalyticalIndexCapstone.lean:104`
  - `lemma FullThermoGeoIndexCapstone.thermodynamicKMSState` — `lean/InfoGeometry/Canonical/AnalyticalIndexCapstone.lean:116`

### `generator`
- declaration matches: `757` (theorem `724`, lemma `33`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/auto_blueprints.lean` (327), `lean/InfoGeometry/Canonical/BohmMadelungOperatorialBridge.lean` (161), `lean/InfoGeometry/Canonical/BekensteinBound.lean` (130), `lean/InfoGeometry/Canonical/BogoliubovTransport.lean` (127)
- sample declarations:
  - `theorem grandCanonicalEulerStep_eq_of_vacuumSplit` — `lean/InfoGeometry/Canonical/AQFTOperatorEndpoints.lean:33`
  - `theorem isStateAlgebraicallyStationary_iff_generatorStationarity` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:110`
  - `theorem starCertifiedEinsteinAnomalyStationary_iff_projectorObstructionStationary_of_projectorAgreement` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:145`
  - `theorem isAlgebraicallyStationary_zero` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:203`
  - `theorem dilation_anomaly_jacobi_expansion` — `lean/InfoGeometry/Canonical/AnomalyDilationBridge.lean:39`
  - `theorem topologicalBekensteinBound_of_sinkhornTrajectory` — `lean/InfoGeometry/Canonical/BekensteinBound.lean:42`
  - `lemma abs_trajectoryRNGenerator_le_trajectoryRNBarrier` — `lean/InfoGeometry/Canonical/BekensteinBound.lean:64`
  - `theorem topologicalBekensteinBound_of_connesCocycle` — `lean/InfoGeometry/Canonical/BekensteinBound.lean:91`

### `chiral`
- declaration matches: `585` (theorem `537`, lemma `48`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/auto_blueprints.lean` (346), `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean` (318), `lean/InfoGeometry/Canonical/SuperchargeEinsteinSourceBridge.lean` (288), `lean/InfoGeometry/Canonical/ConformalProjectorCore.lean` (200)
- sample declarations:
  - `lemma chiralProjectorPlus_neg` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:92`
  - `lemma chiralProjectorMinus_neg` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:100`
  - `lemma analyticalIndex_neg_grading_eq_neg` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:108`
  - `lemma chiralPartPlus_add_chiralPartMinus` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:117`
  - `lemma chiralProjectorPlus_comp_self_of_square_eq_id` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:145`
  - `lemma chiralProjectorMinus_comp_self_of_square_eq_id` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:171`
  - `lemma chiralPartPlus_eq_projectorMinus_comp_of_anticommute` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:198`
  - `lemma chiralPartMinus_eq_projectorPlus_comp_of_anticommute` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:219`

### `potential`
- declaration matches: `464` (theorem `354`, lemma `110`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/auto_blueprints.lean` (361), `lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean` (315), `lean/InfoGeometry/Canonical/BekensteinBound.lean` (139), `lean/InfoGeometry/Canonical/ThermodynamicGenerator.lean` (122)
- sample declarations:
  - `lemma spinFactor_poly_identity` — `lean/InfoGeometry/Architecture/SpinFactor.lean:31`
  - `lemma spinFactorPotential_well_defined` — `lean/InfoGeometry/Architecture/SpinFactor.lean:50`
  - `lemma spinFactorPotential_zero` — `lean/InfoGeometry/Architecture/SpinFactor.lean:58`
  - `theorem measurable_potential` — `lean/InfoGeometry/Basic.lean:64`
  - `theorem measurable_potential_p` — `lean/InfoGeometry/Basic.lean:77`
  - `theorem potential_smul_left_ae` — `lean/InfoGeometry/Basic.lean:84`
  - `theorem potential_smul_right_ae` — `lean/InfoGeometry/Basic.lean:95`
  - `theorem grandCanonicalEulerStep_eq_of_vacuumSplit` — `lean/InfoGeometry/Canonical/AQFTOperatorEndpoints.lean:33`

### `kernel`
- declaration matches: `523` (theorem `498`, lemma `25`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/auto_blueprints.lean` (337), `lean/InfoGeometry/Canonical/ModularSuperchargeClosure.lean` (156), `lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean` (131), `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean` (103)
- sample declarations:
  - `theorem grandCanonicalEulerStep_eq_of_vacuumSplit` — `lean/InfoGeometry/Canonical/AQFTOperatorEndpoints.lean:33`
  - `theorem ibWeightedKMSClosure_of_jointKernel_commutator` — `lean/InfoGeometry/Canonical/AQFTOperatorEndpoints.lean:63`
  - `lemma analyticalIndex_neg_grading_eq_neg` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:108`
  - `lemma analyticalIndex_eq_of_chiralParts_eq` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:255`
  - `theorem chiralSliceIsoAlong_of_const_finrank` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:294`
  - `theorem chiralNoZeroCrossingNear_of_noZeroEigenCrossingNear` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:372`
  - `theorem chiralSlice_finrank_locallyConstant_of_gap` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:418`
  - `theorem chiralNoZeroCrossingAlong_of_gap` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:438`

### `inverse`
- declaration matches: `566` (theorem `533`, lemma `33`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/auto_blueprints.lean` (379), `lean/InfoGeometry/Canonical/ModularSuperchargeClosure.lean` (155), `lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean` (138), `lean/InfoGeometry/Canonical/RelativeModularSingularization.lean` (79)
- sample declarations:
  - `theorem trace_dilation_eq_zero` — `lean/InfoGeometry/Canonical/AnomalyDilationBridge.lean:59`
  - `theorem ChiralAnomaly_is_SkewAdjoint` — `lean/InfoGeometry/Canonical/AnomalyGauge.lean:46`
  - `theorem anomaly_generates_krein_infinitesimal_isometry` — `lean/InfoGeometry/Canonical/AnomalyGauge.lean:80`
  - `theorem anomaly_generates_isometry` — `lean/InfoGeometry/Canonical/AnomalyGauge.lean:93`
  - `theorem starCertifiedEinsteinAnomalyQGT_berry_eq_metricOfOperator_liftedProjectorObstructionOperator_of_projectorAgreement` — `lean/InfoGeometry/Canonical/BerryConnection.lean:754`
  - `theorem informationBerryPhase_eq_loopLength_mul_epsilon_mul_rank` — `lean/InfoGeometry/Canonical/BerryPhase.lean:71`
  - `theorem moorePenroseRightProjector_ne_one_of_hasZeroMode` — `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:81`
  - `theorem moorePenroseLeftProjector_ne_one_of_hasZeroMode` — `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:96`

### `measure`
- declaration matches: `242` (theorem `126`, lemma `116`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/Canonical/IBPythagorean.lean` (302), `lean/InfoGeometry/Canonical/IBFinitePythagorean.lean` (288), `lean/InfoGeometry/Canonical/IBFiniteMonotonicity.lean` (235), `lean/InfoGeometry/auto_blueprints.lean` (167)
- sample declarations:
  - `theorem log_jensen_sum` — `archive/legacy/lean/scratch_convexity.lean:18`
  - `theorem measurable_potential` — `lean/InfoGeometry/Basic.lean:64`
  - `theorem measurable_potential_p` — `lean/InfoGeometry/Basic.lean:77`
  - `theorem potential_smul_left_ae` — `lean/InfoGeometry/Basic.lean:84`
  - `theorem potential_smul_right_ae` — `lean/InfoGeometry/Basic.lean:95`
  - `theorem fiberWeight_singleton_eq_totalWeight` — `lean/InfoGeometry/Canonical/CoarseGraining.lean:45`
  - `theorem encoderMarginal_apply` — `lean/InfoGeometry/Canonical/CoarseGraining.lean:66`
  - `theorem dilation_eq_half_sub_mp_projectors` — `lean/InfoGeometry/Canonical/ConformalProjectorCore.lean:463`

### `audit`
- declaration matches: `14` (theorem `14`, lemma `0`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/Canonical/OperatorialCramerRaoStateFirstSemanticAudit.lean` (25), `lean/InfoGeometry/AuditStrict.lean` (24), `lean/InfoGeometry/auto_blueprints.lean` (18), `lean/InfoGeometry/Meta/Architecture.lean` (9)
- sample declarations:
  - `theorem topicContextPackHealthcheck_ok` — `.agents/workflows/repo-topic-deep-research/templates/lean_context_pack_template.lean:25`
  - `theorem block_diagonal_of_commute_idempotent_similarity` — `lean/InfoGeometry/Canonical/CapstoneSemanticAudit.lean:123`
  - `theorem chunk2_active_only_reduction_audit` — `lean/InfoGeometry/Canonical/OperatorialCramerRaoStateFirstSemanticAudit.lean:51`
  - `theorem chunk3_admissibility_package_audit` — `lean/InfoGeometry/Canonical/OperatorialCramerRaoStateFirstSemanticAudit.lean:72`
  - `theorem chunk3_admissibility_base_audit` — `lean/InfoGeometry/Canonical/OperatorialCramerRaoStateFirstSemanticAudit.lean:102`
  - `theorem chunk3_admissibility_compressed_audit` — `lean/InfoGeometry/Canonical/OperatorialCramerRaoStateFirstSemanticAudit.lean:119`
  - `theorem chunk3_cr_lower_bound_audit` — `lean/InfoGeometry/Canonical/OperatorialCramerRaoStateFirstSemanticAudit.lean:141`
  - `theorem chunk4_measurable_uncertainty_package_audit` — `lean/InfoGeometry/Canonical/OperatorialCramerRaoStateFirstSemanticAudit.lean:159`

### `vacuity`
- declaration matches: `2` (theorem `2`, lemma `0`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/Lint/Vacuity.lean` (32), `lean/InfoGeometry/Meta/Vacuity.lean` (11), `lean/InfoGeometry/Meta/Admission.lean` (7), `lean/InfoGeometry/AuditStrict.lean` (5)
- sample declarations:
  - `theorem spectralProjector_eq_one_of_apex_zero` — `lean/InfoGeometry/Canonical/CapstoneSemanticAudit.lean:50`
  - `theorem vacuity_planner_demo` — `tmp/vacuity_planner_bridge_demo.lean:1`

### `anomaly`
- declaration matches: `376` (theorem `362`, lemma `14`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/auto_blueprints.lean` (369), `lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean` (356), `lean/InfoGeometry/Canonical/ConformalProjectorCore.lean` (241), `lean/InfoGeometry/Canonical/MasterSynthesis.lean` (158)
- sample declarations:
  - `theorem isStateAlgebraicallyStationary_iff_algebraicEinsteinBalance` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:123`
  - `theorem starCertifiedEinsteinAnomalyStationary_iff_projectorObstructionStationary_of_projectorAgreement` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:145`
  - `theorem dilation_anomaly_jacobi_expansion` — `lean/InfoGeometry/Canonical/AnomalyDilationBridge.lean:39`
  - `theorem trace_dilation_eq_zero` — `lean/InfoGeometry/Canonical/AnomalyDilationBridge.lean:59`
  - `theorem normal_phase_of_trace_anomaly_in_finite_dim` — `lean/InfoGeometry/Canonical/AnomalyDilationBridge.lean:77`
  - `lemma commutator_is_skew_adjoint` — `lean/InfoGeometry/Canonical/AnomalyGauge.lean:33`
  - `theorem ChiralAnomaly_is_SkewAdjoint` — `lean/InfoGeometry/Canonical/AnomalyGauge.lean:46`
  - `lemma skew_adjoint_is_krein_skew_adjoint` — `lean/InfoGeometry/Canonical/AnomalyGauge.lean:68`

### `representation`
- declaration matches: `18` (theorem `11`, lemma `7`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/Canonical/TomitaTakesaki.lean` (26), `lean/InfoGeometry/auto_blueprints.lean` (15), `lean/InfoGeometry/Meta/Architecture.lean` (5), `lean/DAG/RepresentationDepthExport.lean` (4)
- sample declarations:
  - `theorem conformal_ward_identity` — `lean/InfoGeometry/Canonical/ConformalWard.lean:31`
  - `lemma cliffordSemanticState_coord_sum_eq_weight_sum` — `lean/InfoGeometry/Canonical/GrandCanonicalExperts.lean:137`
  - `lemma labelGenerator_sq` — `lean/InfoGeometry/Canonical/GrandCanonicalExperts.lean:220`
  - `theorem kAntilinearPart_isKAntilinear` — `lean/InfoGeometry/Canonical/KLinearRepresentation.lean:146`
  - `theorem reflectionQuadratic_nonneg_of_positiveTimeVector` — `lean/InfoGeometry/Canonical/TomitaTakesaki.lean:676`
  - `lemma gen_sq` — `lean/InfoGeometry/Clifford/Cl11Matrix.lean:65`
  - `theorem expPseudoscalar_is_scaling` — `lean/InfoGeometry/Clifford/Hestenes.lean:74`
  - `lemma cl11Rep_pseudoscalar_eq_spectral_epsilon` — `lean/InfoGeometry/Clifford/Hestenes.lean:94`

### `projective`
- declaration matches: `223` (theorem `133`, lemma `90`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/auto_blueprints.lean` (349), `lean/InfoGeometry/Canonical/ProjectiveSplitQ11Realization.lean` (145), `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean` (131), `lean/InfoGeometry/Projective/Dynamics.lean` (92)
- sample declarations:
  - `theorem cl11GlobalGrading_comp_tensor_eq_tensor_comp_cl11GlobalGrading` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:1129`
  - `theorem cl11BottIndexInvariantAlong_of_conjugacy` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:1210`
  - `theorem chiralConjugacyAlong_cl11BottJump_of_projectiveJ` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:1230`
  - `theorem cl11BottAnalyticalIndex_eq_neg_of_projectiveJ` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:1260`
  - `theorem modularTransportFlow_eq_KRotation_of_generator_eq_smul_complex_i` — `lean/InfoGeometry/Canonical/BogoliubovTransport.lean:1038`
  - `theorem cl11BottDirac_comp_tensor_eq_tensor_comp_cl11BottDirac` — `lean/InfoGeometry/Canonical/BottDirac.lean:288`
  - `theorem radialTerm_eq_zero_of_unitRelativeVolume` — `lean/InfoGeometry/Canonical/CalabiYauSingularBridge.lean:56`
  - `theorem logDivergence_eq_singularComplement_of_unitRelativeVolume` — `lean/InfoGeometry/Canonical/CalabiYauSingularBridge.lean:69`

### `drazin`
- declaration matches: `400` (theorem `393`, lemma `7`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/auto_blueprints.lean` (364), `lean/InfoGeometry/Canonical/NavierStokesBridge.lean` (146), `lean/InfoGeometry/Canonical/DrazinSupercharge.lean` (133), `lean/InfoGeometry/Canonical/DrazinInfiniteCore.lean` (124)
- sample declarations:
  - `lemma commutator_is_skew_adjoint` — `lean/InfoGeometry/Canonical/AnomalyGauge.lean:33`
  - `theorem ChiralAnomaly_is_SkewAdjoint` — `lean/InfoGeometry/Canonical/AnomalyGauge.lean:46`
  - `theorem anomaly_generates_krein_infinitesimal_isometry` — `lean/InfoGeometry/Canonical/AnomalyGauge.lean:80`
  - `theorem anomaly_generates_isometry` — `lean/InfoGeometry/Canonical/AnomalyGauge.lean:93`
  - `theorem informationBerryPhase_eq_loopLength_mul_epsilon_mul_rank` — `lean/InfoGeometry/Canonical/BerryPhase.lean:71`
  - `theorem dim_mismatch_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization` — `lean/InfoGeometry/Canonical/BoundaryChiralIndexBridge.lean:53`
  - `theorem moorePenroseLeftProjector_ne_one_of_hasZeroMode` — `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:96`
  - `theorem drazinProjection_ne_one_of_hasZeroMode` — `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:110`

### `clifford`
- declaration matches: `183` (theorem `106`, lemma `77`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/auto_blueprints.lean` (300), `lean/InfoGeometry/Canonical/GrandCanonicalExperts.lean` (215), `lean/InfoGeometry/Quantum/RealMajoranaCategory.lean` (96), `lean/InfoGeometry/Canonical/BottPeriodicity.lean` (90)
- sample declarations:
  - `theorem chiralSliceIsoAlong_of_conjugacy` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:657`
  - `theorem chiralSliceIsoAlong_of_modularCliffordUnitTransport` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:723`
  - `theorem chiralSliceIsoAlong_of_modularCliffordTransport` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:779`
  - `theorem indexInvariantAlong_of_conjugacy` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:839`
  - `theorem indexInvariantAlong_of_modularCliffordTransport` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:854`
  - `theorem indexInvariantAlong_of_modularCliffordTransport_components` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:872`
  - `theorem SinkhornRicciIndexInvariant.mk_components` — `lean/InfoGeometry/Canonical/AnalyticalIndexCoupled.lean:51`
  - `theorem SinkhornRicciIndexInvariant.of_modularCliffordTransport` — `lean/InfoGeometry/Canonical/AnalyticalIndexCoupled.lean:68`

### `semantic`
- declaration matches: `29` (theorem `16`, lemma `13`, axiom `0`)
- lexical hotspots: `lean/Agent/CompilerBridgeCore.lean` (38), `lean/InfoGeometry/Canonical/GrandCanonicalExperts.lean` (32), `lean/InfoGeometry/Canonical/GenerativeInferenceCore.lean` (30), `lean/DAG/ServerExport.lean` (29)
- sample declarations:
  - `theorem block_diagonal_of_commute_idempotent_similarity` — `lean/InfoGeometry/Canonical/CapstoneSemanticAudit.lean:123`
  - `theorem normal_inverse_anomaly_vanishes` — `lean/InfoGeometry/Canonical/ChiralAnomaly.lean:38`
  - `lemma routingChiralAnomaly_eq_semantic_coord_gap` — `lean/InfoGeometry/Canonical/ChiralAnomaly.lean:60`
  - `lemma routingEpsilon_le_one_of_simplex` — `lean/InfoGeometry/Canonical/ChiralAnomaly.lean:75`
  - `lemma routingEpsilon_eq_semantic_gap_abs` — `lean/InfoGeometry/Canonical/ChiralAnomaly.lean:98`
  - `lemma contextSemanticState_fst_eq_plusChannelMass` — `lean/InfoGeometry/Canonical/GenerativeInferenceCore.lean:131`
  - `lemma contextSemanticState_snd_eq_minusChannelMass` — `lean/InfoGeometry/Canonical/GenerativeInferenceCore.lean:137`
  - `lemma contextSemanticState_coord_sum_eq_weight_sum` — `lean/InfoGeometry/Canonical/GenerativeInferenceCore.lean:143`

### `morphism`
- declaration matches: `193` (theorem `117`, lemma `76`, axiom `0`)
- lexical hotspots: `lean/DAG/ExactMorphism.lean` (115), `lean/DAG/ExactMorphismTest.lean` (43), `lean/DAG/Functor.lean` (35), `lean/DAG/CategoryBridge.lean` (27)
- sample declarations:
  - `lemma symmetry_self` — `lean/InfoGeometry/Architecture/SymmetricSpace.lean:28`
  - `theorem grandCanonicalEulerStep_eq_of_vacuumSplit` — `lean/InfoGeometry/Canonical/AQFTOperatorEndpoints.lean:33`
  - `theorem sinkhornIterate_sinkhornKMSCapstone_of_closure` — `lean/InfoGeometry/Canonical/AnalyticalIndexCapstone.lean:51`
  - `theorem fullThermoGeoIndexCapstone_of_states` — `lean/InfoGeometry/Canonical/AnalyticalIndexCapstone.lean:91`
  - `lemma FullThermoGeoIndexCapstone.geometricAlgebraicState` — `lean/InfoGeometry/Canonical/AnalyticalIndexCapstone.lean:104`
  - `lemma FullThermoGeoIndexCapstone.thermodynamicKMSState` — `lean/InfoGeometry/Canonical/AnalyticalIndexCapstone.lean:116`
  - `lemma chiralProjectorPlus_neg` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:92`
  - `lemma chiralProjectorMinus_neg` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:100`

### `information`
- declaration matches: `369` (theorem `333`, lemma `36`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/auto_blueprints.lean` (240), `lean/InfoGeometry/Canonical/RelationalInformationDynamics.lean` (128), `lean/InfoGeometry/Canonical/OnsagerReciprocity.lean` (63), `lean/InfoGeometry/Canonical/VortexReferenceGaugeBridge.lean` (57)
- sample declarations:
  - `theorem grandCanonicalEulerStep_eq_of_vacuumSplit` — `lean/InfoGeometry/Canonical/AQFTOperatorEndpoints.lean:33`
  - `theorem starCertifiedEinsteinAnomalyStationary_iff_projectorObstructionStationary_of_projectorAgreement` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:145`
  - `theorem operatorInformationFirstVariation_neg_left` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:181`
  - `theorem operatorInformationFirstVariation_neg_right` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:192`
  - `theorem isAlgebraicallyStationary_zero` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:203`
  - `theorem isStationaryAlong_of_commute` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:212`
  - `theorem phaseAxisResponse_eq_neg_KVariation` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:234`
  - `theorem KVariation_phaseAxisResponse_eq_neg_modularCurvature` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:247`

### `continuous`
- declaration matches: `489` (theorem `340`, lemma `149`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/Quantum/RealMajorana.lean` (138), `lean/InfoGeometry/Canonical/RestrictedSheetContinuous.lean` (84), `lean/InfoGeometry/Quantum/ModularAnomaly.lean` (73), `lean/InfoGeometry/auto_blueprints.lean` (59)
- sample declarations:
  - `theorem potential_smul_left_ae` — `lean/InfoGeometry/Basic.lean:84`
  - `theorem potential_smul_right_ae` — `lean/InfoGeometry/Basic.lean:95`
  - `theorem expert_apply_mem_transportWeylPlus_of_clm_commutes_transportJ` — `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean:88`
  - `theorem expert_apply_mem_transportWeylMinus_of_clm_commutes_transportJ` — `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean:152`
  - `theorem arnoldNetwork_preserves_transportWeylPlus_of_linearExperts_commute_transportJ` — `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean:260`
  - `theorem arnoldNetwork_preserves_transportWeylMinus_of_linearExperts_commute_transportJ` — `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean:288`
  - `theorem expert_apply_mem_ker_of_clm_commutes` — `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean:318`
  - `theorem deriv_berryOfOperator_expTransport_at` — `lean/InfoGeometry/Canonical/BerryConnection.lean:452`

### `closure`
- declaration matches: `227` (theorem `208`, lemma `19`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/auto_blueprints.lean` (74), `lean/InfoGeometry/Canonical/SinkhornKMSCore.lean` (52), `lean/InfoGeometry/Canonical/SuperchargeCentralChargeClosure.lean` (50), `lean/InfoGeometry/Canonical/RealBdGDIIIAtom.lean` (39)
- sample declarations:
  - `theorem grandCanonicalEulerStep_eq_of_vacuumSplit` — `lean/InfoGeometry/Canonical/AQFTOperatorEndpoints.lean:33`
  - `theorem ibWeightedKMSClosure_of_jointKernel_commutator` — `lean/InfoGeometry/Canonical/AQFTOperatorEndpoints.lean:63`
  - `theorem isStateAlgebraicallyStationary_iff_algebraicEinsteinBalance` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:123`
  - `lemma SinkhornKMSCapstone.kmsState` — `lean/InfoGeometry/Canonical/AnalyticalIndexCapstone.lean:39`
  - `theorem sinkhornIterate_sinkhornKMSCapstone_of_closure` — `lean/InfoGeometry/Canonical/AnalyticalIndexCapstone.lean:51`
  - `theorem fullThermoGeoIndexCapstone_of_states` — `lean/InfoGeometry/Canonical/AnalyticalIndexCapstone.lean:91`
  - `lemma FullThermoGeoIndexCapstone.thermodynamicKMSState` — `lean/InfoGeometry/Canonical/AnalyticalIndexCapstone.lean:116`
  - `theorem chiralNoZeroCrossingAlong_of_gap` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:438`

## Refactored Story

The repository narrative is not a single file stack; it is a layered transport story anchored by declaration-bearing operator geometry.

- **Modular-Operator Spine**: `1157` declaration hits across `modular`.
- **Krein-Clifford Geometry**: `768` declaration hits across `chiral`, `clifford`.
- **Transport-Thermo Layer**: `1136` declaration hits across `transport`.
- **Anomaly-Index-Gravity Layer**: `776` declaration hits across `anomaly`, `drazin`.
- **Methodology and Infrastructure**: `7168` declaration hits across `spectral`, `depth`, `relative`, `metric`, `generator`, `potential`.

In this refactoring, the black-book lane is treated as hypothesis generation, while theorem/lemma/axiom surfaces provide the stable kernel-confirmed memory of the project.
