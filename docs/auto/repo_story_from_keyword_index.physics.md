# Repository Story From Full Lean Keyword Index

- generated: `2026-04-15T21:19:01+00:00`
- git head: `efee09366b90c535fce47f6a0c69b9148b12f508`
- indexed tracked Lean files: `850`
- selector profile: `physics`
- characteristic terms selected: `24`

## Method

1. Full lexical index over all tracked `*.lean` files, sorted by frequency.
2. Characteristic-term selection by count × log(doc-frequency + 1), plus profile-term bias.
3. Deep search over declaration blocks (`theorem`, `lemma`, `axiom`) for each selected term.

## Characteristic Terms

| term | count | doc freq | score | declaration hits |
| --- | ---: | ---: | ---: | ---: |
| `modular` | 9350 | 230 | 50886.61 | 1157 |
| `krein` | 5637 | 349 | 33021.17 | 827 |
| `operator` | 5081 | 291 | 28843.59 | 1048 |
| `spectral` | 5073 | 210 | 27149.98 | 772 |
| `transport` | 4634 | 236 | 25338.99 | 1136 |
| `relative` | 4435 | 145 | 22102.30 | 447 |
| `metric` | 4038 | 176 | 20901.29 | 730 |
| `drazin` | 2323 | 89 | 19453.06 | 400 |
| `generator` | 3477 | 191 | 18280.31 | 757 |
| `clifford` | 1993 | 157 | 18089.75 | 183 |
| `chiral` | 3633 | 141 | 18004.52 | 585 |
| `bogoliubov` | 1555 | 115 | 17891.83 | 384 |
| `depth` | 3100 | 237 | 16964.04 | 1103 |
| `tomita` | 1057 | 85 | 16708.25 | 215 |
| `projective` | 2213 | 114 | 16500.53 | 223 |
| `potential` | 3117 | 177 | 16151.62 | 464 |
| `quantum` | 1824 | 132 | 15920.00 | 207 |
| `weyl` | 1615 | 57 | 15057.62 | 157 |
| `hamiltonian` | 1141 | 62 | 14727.32 | 224 |
| `majorana` | 1411 | 69 | 14494.63 | 242 |
| `sinkhorn` | 889 | 53 | 14046.21 | 156 |
| `einstein` | 1187 | 44 | 14018.51 | 181 |
| `connes` | 335 | 21 | 13035.50 | 51 |
| `kernel` | 2668 | 116 | 12705.48 | 523 |

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

### `krein`
- declaration matches: `827` (theorem `688`, lemma `139`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/auto_blueprints.lean` (675), `lean/InfoGeometry/Krein/KreinSpace.lean` (228), `lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean` (152), `lean/InfoGeometry/Quantum/RealMajoranaCategory.lean` (106)
- sample declarations:
  - `theorem grandCanonicalEulerStep_eq_of_vacuumSplit` — `lean/InfoGeometry/Canonical/AQFTOperatorEndpoints.lean:33`
  - `theorem ibWeightedKMSClosure_of_jointKernel_commutator` — `lean/InfoGeometry/Canonical/AQFTOperatorEndpoints.lean:63`
  - `theorem SinkhornRicciIndexInvariant.of_cl11BottConjugacy` — `lean/InfoGeometry/Canonical/AnalyticalIndexCoupled.lean:134`
  - `theorem ChiralAnomaly_is_SkewAdjoint` — `lean/InfoGeometry/Canonical/AnomalyGauge.lean:46`
  - `lemma skew_adjoint_is_krein_skew_adjoint` — `lean/InfoGeometry/Canonical/AnomalyGauge.lean:68`
  - `theorem anomaly_generates_krein_infinitesimal_isometry` — `lean/InfoGeometry/Canonical/AnomalyGauge.lean:80`
  - `theorem anomaly_generates_isometry` — `lean/InfoGeometry/Canonical/AnomalyGauge.lean:93`
  - `theorem KRotation_add` — `lean/InfoGeometry/Canonical/BerryConnection.lean:255`

### `operator`
- declaration matches: `1048` (theorem `993`, lemma `55`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean` (480), `lean/InfoGeometry/auto_blueprints.lean` (471), `lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean` (314), `lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean` (221)
- sample declarations:
  - `theorem ibWeightedKMSClosure_of_jointKernel_commutator` — `lean/InfoGeometry/Canonical/AQFTOperatorEndpoints.lean:63`
  - `theorem starCertifiedEinsteinAnomalyStationary_iff_projectorObstructionStationary_of_projectorAgreement` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:145`
  - `theorem operatorInformationFirstVariation_neg_left` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:181`
  - `theorem operatorInformationFirstVariation_neg_right` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:192`
  - `theorem isAlgebraicallyStationary_zero` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:203`
  - `theorem isStationaryAlong_of_commute` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:212`
  - `theorem phaseAxisResponse_eq_neg_KVariation` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:234`
  - `theorem KVariation_phaseAxisResponse_eq_neg_modularCurvature` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:247`

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

### `bogoliubov`
- declaration matches: `384` (theorem `377`, lemma `7`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/auto_blueprints.lean` (351), `lean/InfoGeometry/Canonical/BogoliubovFockSuper.lean` (80), `lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean` (68), `lean/InfoGeometry/Canonical/VortexAnomalyLink.lean` (58)
- sample declarations:
  - `theorem grandCanonicalEulerStep_eq_of_vacuumSplit` — `lean/InfoGeometry/Canonical/AQFTOperatorEndpoints.lean:33`
  - `theorem indexInvariantAlong_of_modularCliffordTransport_components` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:872`
  - `theorem expert_apply_mem_transportWeylPlus_of_commutes_transportJ` — `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean:70`
  - `theorem expert_apply_mem_transportWeylPlus_of_clm_commutes_transportJ` — `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean:88`
  - `theorem arnoldNetwork_preserves_transportWeylPlus_of_commutes_transportJ` — `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean:107`
  - `theorem expert_apply_mem_transportWeylMinus_of_commutes_transportJ_and_odd` — `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean:132`
  - `theorem expert_apply_mem_transportWeylMinus_of_clm_commutes_transportJ` — `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean:152`
  - `theorem arnoldNetwork_preserves_transportWeylMinus_of_commutes_transportJ_and_odd` — `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean:173`

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

### `tomita`
- declaration matches: `215` (theorem `211`, lemma `4`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/Canonical/ModularSuperchargeClosure.lean` (160), `lean/InfoGeometry/auto_blueprints.lean` (117), `lean/InfoGeometry/Canonical/StandardFormCore.lean` (51), `lean/InfoGeometry/Canonical/ConnesArakiTomita.lean` (50)
- sample declarations:
  - `theorem starCertifiedEinsteinAnomalyStationary_iff_projectorObstructionStationary_of_projectorAgreement` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:145`
  - `theorem topologicalBekensteinBound_of_connesCocycle_casiniIncrement` — `lean/InfoGeometry/Canonical/BekensteinBound.lean:491`
  - `theorem topologicalBekensteinBound_of_tomitaConnesCocycle_generatorLift` — `lean/InfoGeometry/Canonical/BekensteinBound.lean:533`
  - `theorem topologicalBekensteinBound_of_tomitaConnesCocycle_natMatch` — `lean/InfoGeometry/Canonical/BekensteinBound.lean:558`
  - `theorem topologicalBekensteinBound_of_tomitaConnesCocycle_generatorLift_zero` — `lean/InfoGeometry/Canonical/BekensteinBound.lean:583`
  - `theorem topologicalBekensteinBound_of_tomitaConnesCocycle_casiniIncrement` — `lean/InfoGeometry/Canonical/BekensteinBound.lean:608`
  - `theorem topologicalBekensteinBound_of_tomitaFlowUnitConnesCocycle_casiniIncrement` — `lean/InfoGeometry/Canonical/BekensteinBound.lean:638`
  - `theorem KRotation_add` — `lean/InfoGeometry/Canonical/BerryConnection.lean:255`

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

### `quantum`
- declaration matches: `207` (theorem `189`, lemma `18`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/auto_blueprints.lean` (670), `lean/InfoGeometry/Quantum/QuantumGeometryProjectorBridge.lean` (115), `lean/InfoGeometry/Canonical/PhaseSpaceWeylCausalBridge.lean` (88), `lean/InfoGeometry/Canonical/TopologicalInvariantInvariance.lean` (57)
- sample declarations:
  - `theorem analyticalIndex_eq_zero_time_of_cartanConjugate` — `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:1000`
  - `theorem exists_network_fixed_transportWeylPlus_nonzero_ker_of_experts_fix_of_weylZeroModePair` — `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean:509`
  - `theorem exists_network_fixed_transportWeylMinus_nonzero_ker_of_experts_fix_of_weylZeroModePair` — `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean:553`
  - `theorem exists_network_fixed_transportWeylPlus_nonzero_ker_of_experts_fix_of_simplifiedBoundaryModel_under_bogoliubov` — `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean:597`
  - `theorem exists_network_fixed_transportWeylMinus_nonzero_ker_of_experts_fix_of_simplifiedBoundaryModel_under_bogoliubov` — `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean:638`
  - `theorem KRotation_add` — `lean/InfoGeometry/Canonical/BerryConnection.lean:255`
  - `theorem deriv_berryOfOperator_expTransport_at_zero` — `lean/InfoGeometry/Canonical/BerryConnection.lean:330`
  - `theorem deriv_berryOfOperator_phaseAxisTransport_at_zero_eq_berryOf_phaseAxisResponse` — `lean/InfoGeometry/Canonical/BerryConnection.lean:352`

### `weyl`
- declaration matches: `157` (theorem `132`, lemma `25`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/auto_blueprints.lean` (201), `lean/InfoGeometry/Canonical/PhaseSpaceWeylCausalBridge.lean` (200), `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean` (128), `lean/InfoGeometry/Canonical/WeylTransportChiralBridge.lean` (113)
- sample declarations:
  - `theorem arnoldNetwork_preserves_submodule` — `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean:47`
  - `theorem expert_apply_mem_transportWeylPlus_of_commutes_transportJ` — `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean:70`
  - `theorem expert_apply_mem_transportWeylPlus_of_clm_commutes_transportJ` — `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean:88`
  - `theorem arnoldNetwork_preserves_transportWeylPlus_of_commutes_transportJ` — `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean:107`
  - `theorem expert_apply_mem_transportWeylMinus_of_commutes_transportJ_and_odd` — `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean:132`
  - `theorem expert_apply_mem_transportWeylMinus_of_clm_commutes_transportJ` — `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean:152`
  - `theorem arnoldNetwork_preserves_transportWeylMinus_of_commutes_transportJ_and_odd` — `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean:173`
  - `theorem arnoldNetwork_preserves_base` — `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean:199`

### `hamiltonian`
- declaration matches: `224` (theorem `200`, lemma `24`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/Canonical/ModularSuperchargeClosure.lean` (170), `lean/InfoGeometry/auto_blueprints.lean` (150), `lean/InfoGeometry/Canonical/DrazinSupercharge.lean` (83), `lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean` (83)
- sample declarations:
  - `theorem grandCanonicalEulerStep_eq_of_vacuumSplit` — `lean/InfoGeometry/Canonical/AQFTOperatorEndpoints.lean:33`
  - `theorem anticommutator_bogoliubov_eq_zero_of_coeff_eq_inducedChemicalPotential_of_vacuumTransported` — `lean/InfoGeometry/Canonical/BogoliubovFockSuper.lean:876`
  - `lemma grandCanonicalGenerator_eq_hamiltonian_of_vacuumTransported` — `lean/InfoGeometry/Canonical/BogoliubovFockSuper.lean:897`
  - `lemma grandCanonicalFockGenerator_eq_hamiltonian_of_vacuumTransported` — `lean/InfoGeometry/Canonical/BogoliubovFockSuper.lean:914`
  - `theorem projectiveDensityWeightHamiltonianProfile_zero` — `lean/InfoGeometry/Canonical/DensityWeightIntertwinerBridge.lean:85`
  - `theorem projectiveDensityWeightHamiltonianProfile_eq_relativeModularPotential_countRay_add_weightShift` — `lean/InfoGeometry/Canonical/DensityWeightIntertwinerBridge.lean:97`
  - `theorem metricOp_eq_relativeTomitaTakesakiOp_of_isDiagonalRelativeCountMetricSlice` — `lean/InfoGeometry/Canonical/DiagonalMetricModularBridge.lean:82`
  - `theorem metricOp_eq_countModularHamiltonian_of_isDiagonalRelativeCountMetricSlice` — `lean/InfoGeometry/Canonical/DiagonalMetricModularBridge.lean:97`

### `majorana`
- declaration matches: `242` (theorem `229`, lemma `13`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/auto_blueprints.lean` (235), `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean` (194), `lean/InfoGeometry/Quantum/RealMajoranaCategory.lean` (126), `lean/InfoGeometry/Canonical/KramersMajoranaCompatibility.lean` (67)
- sample declarations:
  - `theorem arnoldNetwork_preserves_submodule` — `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean:47`
  - `theorem expert_apply_mem_transportWeylPlus_of_commutes_transportJ` — `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean:70`
  - `theorem expert_apply_mem_transportWeylPlus_of_clm_commutes_transportJ` — `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean:88`
  - `theorem arnoldNetwork_preserves_transportWeylPlus_of_commutes_transportJ` — `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean:107`
  - `theorem expert_apply_mem_transportWeylMinus_of_commutes_transportJ_and_odd` — `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean:132`
  - `theorem expert_apply_mem_transportWeylMinus_of_clm_commutes_transportJ` — `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean:152`
  - `theorem arnoldNetwork_preserves_transportWeylMinus_of_commutes_transportJ_and_odd` — `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean:173`
  - `theorem arnoldNetwork_preserves_base` — `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean:199`

### `sinkhorn`
- declaration matches: `156` (theorem `108`, lemma `48`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/Canonical/SinkhornFoundation.lean` (183), `lean/InfoGeometry/auto_blueprints.lean` (115), `lean/InfoGeometry/Canonical/ChiralAnomaly.lean` (93), `lean/InfoGeometry/Canonical/SinkhornKMSCore.lean` (57)
- sample declarations:
  - `theorem grandCanonicalEulerStep_eq_of_vacuumSplit` — `lean/InfoGeometry/Canonical/AQFTOperatorEndpoints.lean:33`
  - `theorem ibWeightedKMSClosure_of_jointKernel_commutator` — `lean/InfoGeometry/Canonical/AQFTOperatorEndpoints.lean:63`
  - `lemma SinkhornKMSCapstone.kmsState` — `lean/InfoGeometry/Canonical/AnalyticalIndexCapstone.lean:39`
  - `theorem sinkhornIterate_sinkhornKMSCapstone_of_closure` — `lean/InfoGeometry/Canonical/AnalyticalIndexCapstone.lean:51`
  - `theorem fullThermoGeoIndexCapstone_of_states` — `lean/InfoGeometry/Canonical/AnalyticalIndexCapstone.lean:91`
  - `lemma FullThermoGeoIndexCapstone.geometricAlgebraicState` — `lean/InfoGeometry/Canonical/AnalyticalIndexCapstone.lean:104`
  - `lemma FullThermoGeoIndexCapstone.thermodynamicKMSState` — `lean/InfoGeometry/Canonical/AnalyticalIndexCapstone.lean:116`
  - `theorem SinkhornRicciIndexInvariant.mk_components` — `lean/InfoGeometry/Canonical/AnalyticalIndexCoupled.lean:51`

### `einstein`
- declaration matches: `181` (theorem `166`, lemma `15`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean` (169), `lean/InfoGeometry/Canonical/MasterSynthesis.lean` (107), `lean/InfoGeometry/auto_blueprints.lean` (101), `lean/InfoGeometry/Canonical/RicciMongeAmpere.lean` (89)
- sample declarations:
  - `theorem grandCanonicalEulerStep_eq_of_vacuumSplit` — `lean/InfoGeometry/Canonical/AQFTOperatorEndpoints.lean:33`
  - `theorem einsteinHilbertAction_eq_neg_six_dual_pairing_sub_dual_of_compatible` — `lean/InfoGeometry/Canonical/ActionDuality.lean:39`
  - `theorem einsteinHilbertAction_and_zeroGap_of_compatible` — `lean/InfoGeometry/Canonical/ActionDuality.lean:58`
  - `theorem isStateAlgebraicallyStationary_iff_algebraicEinsteinBalance` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:123`
  - `theorem starCertifiedEinsteinAnomalyStationary_iff_projectorObstructionStationary_of_projectorAgreement` — `lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:145`
  - `theorem hestenesWeylModularBerryTwoForm_eq_berryOf_hestenesWeylConnectionGenerator_add_relativeModularSourceDeriv_of_commute_gaugePart` — `lean/InfoGeometry/Canonical/BerryConnection.lean:728`
  - `theorem starCertifiedEinsteinAnomalyQGT_berry_eq_metricOfOperator_liftedProjectorObstructionOperator_of_projectorAgreement` — `lean/InfoGeometry/Canonical/BerryConnection.lean:754`
  - `theorem cliffordConcreteIsCARPair` — `lean/InfoGeometry/Canonical/BogoliubovFockSuper.lean:770`

### `connes`
- declaration matches: `51` (theorem `50`, lemma `1`, axiom `0`)
- lexical hotspots: `lean/InfoGeometry/Canonical/MasterSynthesis.lean` (58), `lean/InfoGeometry/Canonical/BekensteinBound.lean` (47), `lean/InfoGeometry/Canonical/YangMillsContinuum.lean` (38), `lean/InfoGeometry/auto_blueprints.lean` (37)
- sample declarations:
  - `lemma abs_trajectoryRNGenerator_le_trajectoryRNBarrier` — `lean/InfoGeometry/Canonical/BekensteinBound.lean:64`
  - `theorem topologicalBekensteinBound_of_connesCocycle` — `lean/InfoGeometry/Canonical/BekensteinBound.lean:91`
  - `theorem cocycleEntropyPotential_natMatch_of_cocycleGeneratorLift_zero` — `lean/InfoGeometry/Canonical/BekensteinBound.lean:214`
  - `theorem cocycleEntropyPotential_natMatch_of_connesCocycle_generatorLift` — `lean/InfoGeometry/Canonical/BekensteinBound.lean:278`
  - `theorem cocycleGeneratorLift_iff_natMatch_of_connesCocycle` — `lean/InfoGeometry/Canonical/BekensteinBound.lean:299`
  - `theorem topologicalBekensteinBound_of_connesCocycle_generatorLift` — `lean/InfoGeometry/Canonical/BekensteinBound.lean:324`
  - `theorem cocycleIncrement_abs_le_trajectoryRNBarrier_of_connesCocycle_generatorLift` — `lean/InfoGeometry/Canonical/BekensteinBound.lean:355`
  - `theorem topologicalBekensteinBound_of_connesCocycle_natMatch` — `lean/InfoGeometry/Canonical/BekensteinBound.lean:384`

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

## Refactored Story

The repository narrative is not a single file stack; it is a layered transport story anchored by declaration-bearing operator geometry.

- **Modular-Operator Spine**: `1647` declaration hits across `modular`, `tomita`, `hamiltonian`, `connes`.
- **Krein-Clifford Geometry**: `1837` declaration hits across `krein`, `clifford`, `chiral`, `majorana`.
- **Transport-Thermo Layer**: `1676` declaration hits across `transport`, `bogoliubov`, `sinkhorn`.
- **Anomaly-Index-Gravity Layer**: `738` declaration hits across `drazin`, `weyl`, `einstein`.
- **Methodology and Infrastructure**: `6274` declaration hits across `operator`, `spectral`, `relative`, `metric`, `generator`, `depth`.

In this refactoring, the black-book lane is treated as hypothesis generation, while theorem/lemma/axiom surfaces provide the stable kernel-confirmed memory of the project.
