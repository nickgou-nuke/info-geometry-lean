# Process Flow Defect Report

Input dir: `/home/goutev/LEAN4/info-geometry-lean/artifacts/dag/process-flow`
Derived cocycles: `/home/goutev/LEAN4/info-geometry-lean/artifacts/dag/process-flow/flow-cocycles.jsonl`
Derived comparisons: `/home/goutev/LEAN4/info-geometry-lean/artifacts/dag/process-flow/comparison-candidates.jsonl`

Derived analysis over constitutive process-flow artifacts; no analyzer output is fed back into Lean classification.
Path rows are bounded ancestry candidates exported from Lean, not an exhaustive enumeration of all derivational paths in the dependency DAG.
Path debt is reported in two forms: exported residual debt from Lean's bounded path candidates, and pairwise-confirmed residual debt from unresolved comparison pairs recognized by this analyzer.

## Summary

- Flow edges: `9578`
- Process events: `2825`
- Path candidates: `15841`
- Comparison candidates: `20000`
- Unresolved comparison pairs: `1273`
- Defect rows: `2909`
- Cocycle rows: `9578`
- Exported path residual debt total: `2533`
- Pairwise-confirmed residual debt total: `2546`
- Effective path residual debt total: `5079`
- Paths with exported residual debt: `2337`
- Paths with pairwise-confirmed residual debt: `516`
- Paths with effective residual debt: `2756`

## Defects By Kind

| Defect | Count | Severity Weight |
| --- | --- | --- |
| unresolvedComparison | 2372 | 1 |
| remoteAttachment | 262 | 3 |
| mixedPolarity | 99 | 2 |
| boundaryBypass | 80 | 4 |
| failedLocalFactorization | 80 | 3 |
| illicitBoundaryCrossing | 14 | 5 |
| regressiveFlow | 2 | 5 |

## Most Stressed Declarations

| Node | Stress | Local | ExportedPath | PairwisePath | SourceDefects | Boundary | Role |
| --- | --- | --- | --- | --- | --- | --- | --- |
| InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationFirstVariation | 754 | 0 | 8 | 746 | 0 | internal | vertical |
| InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationMixedSecondVariation | 351 | 0 | 33 | 318 | 0 | internal | vertical |
| InfoGeometry.Canonical.MoE.ExpertIdx | 274 | 274 | 0 | 0 | 0 | internal | vertical |
| InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationHessian | 234 | 0 | 15 | 219 | 0 | internal | vertical |
| InfoGeometry.Canonical.Drazin.IsDrazinInverse | 200 | 0 | 1 | 199 | 0 | internal | vertical |
| InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection | 187 | 0 | 5 | 182 | 0 | internal | vertical |
| InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.exists_nontrivial_regularization_pair_of_dim_mismatch | 154 | 0 | 0 | 154 | 0 | internal | vertical |
| InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.supercharge | 151 | 67 | 84 | 0 | 0 | internal | vertical |
| InfoGeometry.Canonical.AlgebraicStationarity.modularCurvatureExpectation_eq_zero_of_phaseResponseStationary | 134 | 0 | 0 | 134 | 0 | internal | vertical |
| InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.exists_nontrivial_regularization_pair_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel | 133 | 0 | 0 | 133 | 0 | internal | vertical |
| InfoGeometry.Canonical.BoundaryLocalizationIndexEquiv.boundaryScale_ne_zero_iff_boundaryGenerator_ne_zero | 132 | 0 | 6 | 126 | 0 | internal | vertical |
| InfoGeometry.Canonical.DrazinSupercharge.commutator | 127 | 61 | 66 | 0 | 0 | internal | vertical |

## Most Stressed Modules

| Module | Nodes | Stress | Local | ExportedPath | PairwisePath | SourceDefects | Credit |
| --- | --- | --- | --- | --- | --- | --- | --- |
| InfoGeometry.Canonical.RelationalInformationDynamics | 44 | 1739 | 0 | 158 | 1581 | 36 | 935 |
| InfoGeometry.Canonical.AlgebraicStationarity | 18 | 810 | 0 | 4 | 806 | 4 | 285 |
| InfoGeometry.Canonical.MixtureOfExperts | 10 | 750 | 717 | 33 | 0 | 0 | 189 |
| InfoGeometry.Canonical.DrazinSupercharge | 69 | 652 | 160 | 488 | 4 | 115 | 2324 |
| InfoGeometry.Canonical.Drazin | 21 | 429 | 0 | 6 | 423 | 0 | 354 |
| InfoGeometry.Canonical.BulkBoundaryRegularizationBridge | 11 | 407 | 10 | 16 | 381 | 5 | 380 |
| InfoGeometry.Canonical.BoundaryLocalizationIndexEquiv | 10 | 388 | 0 | 24 | 364 | 18 | 561 |
| InfoGeometry.Canonical.OperatorialCramerRaoStateFirstSemanticAudit | 10 | 375 | 70 | 305 | 0 | 115 | 746 |
| InfoGeometry.Canonical.RelativeModularOperator | 24 | 314 | 250 | 64 | 0 | 96 | 579 |
| InfoGeometry.KK.DiracFredholmIndex | 14 | 300 | 4 | 295 | 1 | 0 | 366 |
| InfoGeometry.Canonical.RelationalInformationCore | 28 | 275 | 8 | 241 | 26 | 3 | 585 |
| InfoGeometry.LLM.ScalarThermoBridge | 9 | 265 | 260 | 5 | 0 | 84 | 137 |

## Most Anomalous Edges

| Edge | Grade | Debt | Net | Role | Boundary | Tags |
| --- | --- | --- | --- | --- | --- | --- |
| InfoGeometry.LLM.AllTopThermodynamicRouter.allTopWeight_eq_finiteGibbs -> InfoGeometry.Canonical.MoE.ExpertIdx | unclear | 17 | -13 | remoteSupport | mixed | remoteAttachment, boundaryBypass, failedLocalFactorization, illicitBoundaryCrossing, mixedPolarity |
| InfoGeometry.LLM.AllTopThermodynamicRouter.allTopWeight_eq_finiteGibbs -> InfoGeometry.Canonical.MoE.normalizedWeights | unclear | 17 | -13 | remoteSupport | mixed | remoteAttachment, boundaryBypass, failedLocalFactorization, illicitBoundaryCrossing, mixedPolarity |
| InfoGeometry.LLM.KMSSoftmaxBridge.softmaxWeight_eq_kmsWeight -> InfoGeometry.Canonical.MoE.ExpertIdx | unclear | 17 | -13 | remoteSupport | mixed | remoteAttachment, boundaryBypass, failedLocalFactorization, illicitBoundaryCrossing, mixedPolarity |
| InfoGeometry.LLM.HypothesisScaffold70.h70_scale_shape_split -> InfoGeometry.Canonical.MoE.normalizedMixture | remote_descent | 10 | -9 | remoteSupport | unclear | remoteAttachment, boundaryBypass, failedLocalFactorization |
| InfoGeometry.LLM.RouterFreeEnergyBridge.routerScaledPotentialGap_eq_scaledBregman -> InfoGeometry.Canonical.MoE.ExpertIdx | remote_descent | 10 | -9 | remoteSupport | unclear | remoteAttachment, boundaryBypass, failedLocalFactorization |
| InfoGeometry.LLM.RouterFreeEnergyBridge.routerScaledPotentialGap_eq_scaledBregman -> InfoGeometry.Canonical.MoE.routerEnergy | remote_descent | 10 | -9 | remoteSupport | unclear | remoteAttachment, boundaryBypass, failedLocalFactorization |
| InfoGeometry.LLM.ScalarThermoBridge.switchMatrix_mem_rowStochastic_bridge -> InfoGeometry.Canonical.MoE.switchMatrix | remote_descent | 10 | -9 | remoteSupport | unclear | remoteAttachment, boundaryBypass, failedLocalFactorization |
| InfoGeometry.LLM.ThermodynamicSwitching.exists_modewiseClifford_rep_of_bistochastic_switch -> InfoGeometry.Canonical.MoE.PermMode | remote_descent | 10 | -9 | remoteSupport | unclear | remoteAttachment, boundaryBypass, failedLocalFactorization |
| InfoGeometry.LLM.ThermodynamicSwitching.exists_modewiseClifford_rep_of_bistochastic_switch -> InfoGeometry.Canonical.MoE.SplitCliffordAlg | remote_descent | 10 | -9 | remoteSupport | unclear | remoteAttachment, boundaryBypass, failedLocalFactorization |
| InfoGeometry.LLM.ThermodynamicSwitching.exists_modewiseClifford_rep_of_bistochastic_switch -> InfoGeometry.Canonical.MoE.switchMatrix | remote_descent | 10 | -9 | remoteSupport | unclear | remoteAttachment, boundaryBypass, failedLocalFactorization |
| InfoGeometry.LLM.ThermodynamicSwitching.exists_modewiseClifford_rep_of_bistochastic_switch -> InfoGeometry.Canonical.MoE.weightedModeCliffordState | remote_descent | 10 | -9 | remoteSupport | unclear | remoteAttachment, boundaryBypass, failedLocalFactorization |
| InfoGeometry.LLM.ThermodynamicSwitching.exists_modewiseClifford_rep_of_bistochastic_switch -> InfoGeometry.Canonical.MoE.weightedModeCliffordStateMinus | remote_descent | 10 | -9 | remoteSupport | unclear | remoteAttachment, boundaryBypass, failedLocalFactorization |

## Best Low-Defect Bridges

| Edge | Grade | Credit | Net | Role | Boundary | Use |
| --- | --- | --- | --- | --- | --- | --- |
| InfoGeometry.Canonical.BohmMadelungOperatorialBridge.potentialDatum_constantStateGeneratorField_kSplitReadout_stationary_iff_isPotentialKillingOperator -> InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum | adjacent_descent | 12 | 12 | transportArg | bridge | both |
| InfoGeometry.Canonical.BohmMadelungOperatorialBridge.potentialDatum_constantStateGeneratorField_stateQGTReadout_pair_eq_comparisonReadout_pair -> InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum | adjacent_descent | 12 | 12 | transportArg | bridge | both |
| InfoGeometry.Canonical.BohmMadelungOperatorialBridge.potentialDatum_constantStateGeneratorField_stateQGTReadout_stationary_iff_isPotentialKillingOperator -> InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum | adjacent_descent | 12 | 12 | transportArg | bridge | both |
| InfoGeometry.Canonical.BoundaryChiralIndexBridge.dim_mismatch_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization -> InfoGeometry.Canonical.OperatorialCentralCharge.operatorialCentralCharge | adjacent_descent | 12 | 12 | transportArg | bridge | both |
| InfoGeometry.Canonical.BoundaryChiralIndexBridge.dim_mismatch_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization -> InfoGeometry.KK.RealSplitKreinDiracFredholmModule | adjacent_descent | 12 | 12 | transportArg | bridge | both |
| InfoGeometry.Canonical.BoundaryChiralIndexBridge.dim_mismatch_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization -> InfoGeometry.KK.RealSplitKreinKasparovCycle.ChiralFredholmSurface | adjacent_descent | 12 | 12 | transportArg | bridge | both |
| InfoGeometry.Canonical.BoundaryLocalizationIndexEquiv.operatorialCentralChargeParity_ne_zero_boundaryGenerator_ne_zero_of_identifiedTransportedPolarization -> InfoGeometry.KK.RealSplitKreinDiracFredholmModule | adjacent_descent | 12 | 12 | transportArg | bridge | both |
| InfoGeometry.Canonical.BoundaryLocalizationIndexEquiv.operatorialCentralChargeParity_ne_zero_boundaryGenerator_ne_zero_of_identifiedTransportedPolarization -> InfoGeometry.KK.RealSplitKreinKasparovCycle.ChiralFredholmSurface | adjacent_descent | 12 | 12 | transportArg | bridge | both |
| InfoGeometry.Canonical.BoundaryLocalizationIndexEquiv.operatorialCentralChargeParity_ne_zero_boundaryGenerator_ne_zero_of_kernelSeparation_of_identifiedTransportedPolarization -> InfoGeometry.KK.RealSplitKreinDiracFredholmModule | adjacent_descent | 12 | 12 | transportArg | bridge | both |
| InfoGeometry.Canonical.BoundaryLocalizationIndexEquiv.operatorialCentralChargeParity_ne_zero_boundaryGenerator_ne_zero_of_kernelSeparation_of_identifiedTransportedPolarization -> InfoGeometry.KK.RealSplitKreinKasparovCycle.ChiralFredholmSurface | adjacent_descent | 12 | 12 | transportArg | bridge | both |
| InfoGeometry.Canonical.BoundaryLocalizationIndexEquiv.operatorialCentralChargeParity_ne_zero_coriolisVorticity_ne_zero_of_identifiedTransportedPolarization -> InfoGeometry.KK.RealSplitKreinDiracFredholmModule | adjacent_descent | 12 | 12 | transportArg | bridge | both |
| InfoGeometry.Canonical.BoundaryLocalizationIndexEquiv.operatorialCentralChargeParity_ne_zero_coriolisVorticity_ne_zero_of_identifiedTransportedPolarization -> InfoGeometry.KK.RealSplitKreinKasparovCycle.ChiralFredholmSurface | adjacent_descent | 12 | 12 | transportArg | bridge | both |

## Unresolved Comparison Candidates

| PathA | PathB | Evidence | RoleMatch | SupportDiv | Witnesses | BestScore |
| --- | --- | --- | --- | --- | --- | --- |
| 0 | 19 | parallel_transport | 1.0 | 0.0 | 0 | 0 |
| 0 | 32 | parallel_transport | 1.0 | 0.0 | 0 | 0 |
| 0 | 34 | parallel_transport | 1.0 | 0.0 | 0 | 0 |
| 0 | 45 | parallel_transport | 1.0 | 0.0 | 0 | 0 |
| 2 | 4 | parallel_transport | 1.0 | 0.0 | 0 | 0 |
| 2 | 13 | parallel_transport | 1.0 | 0.0 | 0 | 0 |
| 2 | 20 | parallel_transport | 1.0 | 0.0 | 0 | 0 |
| 2 | 31 | parallel_transport | 1.0 | 0.0 | 0 | 0 |
| 2 | 33 | parallel_transport | 1.0 | 0.0 | 0 | 0 |
| 2 | 37 | parallel_transport | 1.0 | 0.0 | 0 | 0 |
| 2 | 42 | parallel_transport | 1.0 | 0.0 | 0 | 0 |
| 2 | 43 | parallel_transport | 1.0 | 0.0 | 0 | 0 |

## Most Stressed Path Candidates

| Path | Steps | ExportedResidual | PairwiseResidual | UnresolvedPairs | PathDefectCost | EdgeAccumDebt | Net |
| --- | --- | --- | --- | --- | --- | --- | --- |
| InfoGeometry.Canonical.AlgebraicStationarity.modularCurvatureOperator -> InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationMixedSecondVariation | 2 | 0 | 62 | 62 | 0 | 0 | 18 |
| InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.exists_nontrivial_regularization_pair_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel -> InfoGeometry.Canonical.Drazin.IsDrazinInverse | 2 | 0 | 57 | 57 | 0 | 0 | 18 |
| InfoGeometry.Canonical.AlgebraicStationarity.modularCurvatureExpectation_eq_zero_of_phaseResponseStationary -> InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationMixedSecondVariation | 2 | 0 | 53 | 53 | 0 | 0 | 18 |
| InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.exists_nontrivial_regularization_pair_of_dim_mismatch -> InfoGeometry.Canonical.Drazin.IsDrazinInverse | 1 | 0 | 46 | 46 | 0 | 0 | 9 |
| InfoGeometry.Canonical.AlgebraicStationarity.modularCurvatureExpectation_eq_zero_of_phaseResponseStationary -> InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationHessian | 2 | 0 | 44 | 44 | 0 | 0 | 18 |
| InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.exists_nontrivial_regularization_pair_of_dim_mismatch -> InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection | 1 | 0 | 43 | 43 | 0 | 0 | 9 |
| InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.exists_nontrivial_regularization_pair_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel -> InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection | 1 | 0 | 43 | 43 | 0 | 0 | 9 |
| InfoGeometry.Canonical.AlgebraicStationarity.KVariation_phaseAxisResponse_eq_neg_modularCurvature -> InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationMixedSecondVariation | 1 | 0 | 41 | 41 | 0 | 0 | 9 |
| InfoGeometry.Canonical.AlgebraicStationarity.modularCurvatureOperator -> InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationHessian | 1 | 0 | 41 | 41 | 0 | 0 | 9 |
| InfoGeometry.Canonical.AlgebraicStationarity.IsAlgebraicallyStationary -> InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationFirstVariation | 2 | 0 | 36 | 36 | 0 | 0 | 18 |
| InfoGeometry.Canonical.AlgebraicStationarity.isAlgebraicallyStationary_of_central -> InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationFirstVariation | 2 | 0 | 36 | 36 | 0 | 0 | 18 |
| InfoGeometry.Canonical.AlgebraicStationarity.IsStationaryAlong -> InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationFirstVariation | 1 | 0 | 33 | 33 | 0 | 0 | 9 |
