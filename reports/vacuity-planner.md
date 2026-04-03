# Vacuity Planner Report

## Boundary

- plannerMode: planning-only
- mutationSurface: False
- automaticReplacement: False
- proofRepair: False

## Input Coverage

- theoremSignificanceEntries: 5055
- declarationCount: 8295
- edgeCount: 53644
- ownerEntries: 7
- bridgePayloadFiles: 1
- bridgePayloadObjects: 1

## Normalization Snapshot

### Top exprSemantic head groups

| rank | surface | head | count | confidence |
|---:|---|---|---:|---:|
| 1 | local | Prop | 1 | 0.82 |
| 2 | local | p | 1 | 0.82 |
| 3 | target | p | 1 | 0.82 |

### Top fingerprint groups

| rank | surface | fingerprint | count | confidence |
|---:|---|---|---:|---:|
| 1 | local | shape/v1/head:fvar | 1 | 0.82 |
| 2 | local | shape/v1/head:sort:prop | 1 | 0.82 |
| 3 | target | shape/v1/head:fvar | 1 | 0.82 |

## Ranked Vacuity Candidates

| rank | declaration | score | confidence |
|---|---|---|---|
| 1 | InfoGeometry.Krein.HilbertDoubled.ext_iff | 1.0 | 0.8544 |
| 2 | InfoGeometry.Krein.NeutralSpace.ext_iff | 1.0 | 0.8544 |
| 3 | InfoGeometry.Canonical.AQFTOperatorInterface.ibWeightedKMSClosure_of_jointKernel_commutator | 0.93 | 0.8495 |
| 4 | InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex_eq_of_chiralParts_eq | 0.93 | 0.8495 |
| 5 | InfoGeometry.Canonical.AnalyticalIndex.chiralSliceIsoAlong_of_noZeroEigenCrossing_path | 0.93 | 0.8495 |
| 6 | InfoGeometry.Canonical.AnalyticalIndex.cl11_bottDirac_sq_eq_zero_of_laplacian_zero | 0.93 | 0.8495 |
| 7 | InfoGeometry.Canonical.AnalyticalIndex.indexInvariantAlong_of_noZeroEigenCrossing_path | 0.93 | 0.8495 |
| 8 | InfoGeometry.Canonical.Attention.euclideanAttentionWeights_sum_one | 0.93 | 0.8495 |
| 9 | InfoGeometry.Canonical.Attention.exists_perm_decomposition_of_bistochastic_polarizedPlusAttention | 0.93 | 0.8495 |
| 10 | InfoGeometry.Canonical.Attention.lorentzianAttentionWeights_sum_one | 0.93 | 0.8495 |
| 11 | InfoGeometry.Canonical.Attention.polarizedPlusAttentionHead_eq_euclideanAttentionHead_of_constantKeyNorm | 0.93 | 0.8495 |
| 12 | InfoGeometry.Canonical.Attention.polarizedPlusAttentionHead_eq_gibbsExpectation | 0.93 | 0.8495 |
| 13 | InfoGeometry.Canonical.Attention.polarizedPlusAttentionWeights_eq_euclideanGibbsWeights_of_constantKeyNorm | 0.93 | 0.8495 |
| 14 | InfoGeometry.Canonical.Attention.polarizedPlusParams_energy_eq_neg_dot_plus_half_norms | 0.93 | 0.8495 |
| 15 | InfoGeometry.Canonical.BekensteinBound.relEnt_drop_nonneg_of_casiniIncrementBridge | 0.93 | 0.8495 |
| 16 | InfoGeometry.Canonical.BekensteinBound.topologicalBekensteinBound_of_connesCocycle | 0.93 | 0.8495 |
| 17 | InfoGeometry.Canonical.BekensteinBound.topologicalBekensteinBound_of_tomitaConnesCocycle_generatorLift | 0.93 | 0.8495 |
| 18 | InfoGeometry.Canonical.BeliefAlgebra.BeliefSystem.non_commutative_updates | 0.93 | 0.8495 |
| 19 | InfoGeometry.Canonical.BogoliubovClosedForms.JBoost_apply | 0.93 | 0.8495 |
| 20 | InfoGeometry.Canonical.BogoliubovClosedForms.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace | 0.93 | 0.8495 |

## Ranked Owner Candidates

| rank | ownerFile | score | confidence |
|---|---|---|---|
| 1 | lean/InfoGeometry/Canonical/InformationPartitionCore.lean | 1.0 | 0.72 |
| 2 | lean/InfoGeometry/Canonical/PositiveRayCore.lean | 1.0 | 0.72 |
| 3 | lean/InfoGeometry/Canonical/RelativePotentialCore.lean | 1.0 | 0.72 |
| 4 | lean/InfoGeometry/Krein/PolarizedSector.lean | 0.4 | 0.72 |
| 5 | lean/InfoGeometry/Krein/SplitQuadratic.lean | 0.4 | 0.72 |
| 6 | lean/InfoGeometry/Krein/SplitQuadraticSheets.lean | 0.4 | 0.72 |

## Ranked Replacement Candidates

| rank | replacementDecl | score | confidence |
|---|---|---|---|
| 1 | InfoGeometry.Krein.cl11RepLin | 1.0 | 0.84 |
| 2 | InfoGeometry.Krein.cl11RepLin_apply_to_doubled | 1.0 | 0.84 |
| 3 | InfoGeometry.Quantum.RealMajoranaCategory.SplitCliffordDatum.Mode | 1.0 | 0.8267 |
| 4 | InfoGeometry.Quantum.RealMajoranaCategory.cl11DoubledCore | 1.0 | 0.8267 |
| 5 | InfoGeometry.Quantum.RealMajoranaCategory.cl11SplitCliffordDatum | 1.0 | 0.8267 |
| 6 | InfoGeometry.Canonical.Attention.attentionWeights | 1.0 | 0.8262 |
| 7 | InfoGeometry.Canonical.BogoliubovFockSuper.superBracket | 1.0 | 0.8262 |
| 8 | InfoGeometry.Canonical.BogoliubovFockSuper.superBracket_even_left | 1.0 | 0.8262 |
| 9 | InfoGeometry.Canonical.Attention.attentionWeights_sum_one | 1.0 | 0.8232 |
| 10 | InfoGeometry.Canonical.BogoliubovFockSuper.anticommutator | 1.0 | 0.8031 |
| 11 | InfoGeometry.Canonical.BottDirac.Endomorphism | 1.0 | 0.8011 |
| 12 | InfoGeometry.Canonical.AnalyticalIndex.ChiralNoZeroEigenCrossingNear | 1.0 | 0.8011 |
| 13 | InfoGeometry.Krein.to_doubled | 1.0 | 0.8011 |
| 14 | InfoGeometry.Quantum.annihilationOp | 1.0 | 0.8011 |
| 15 | InfoGeometry.Quantum.creationOp | 1.0 | 0.8011 |
| 16 | InfoGeometry.Krein.DoubledSpace | 1.0 | 0.7963 |
| 17 | InfoGeometry.Canonical.RicciMongeAmpere.RicciTensor | 1.0 | 0.7948 |
| 18 | InfoGeometry.Krein.HilbertDoubled | 1.0 | 0.7892 |
| 19 | InfoGeometry.Krein.HilbertDoubled.val | 1.0 | 0.7892 |
| 20 | InfoGeometry.Krein.NeutralSpace | 1.0 | 0.7892 |

## Confidence Provenance Weights

- headSourceWeight: {"exprSemantic": 1.0, "textHeuristic": 0.55, "unavailable": 0.2}
- diagnosticProvenanceWeight: {"bridgeRule": 0.6, "fallback": 0.4, "leanTag": 1.0, "messagePattern": 0.75}
- violationLevelWeight: {"error": 1.0, "info": 0.45, "warning": 0.7}
