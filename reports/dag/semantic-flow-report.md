# Semantic Flow Report

This report interprets process-flow artifacts as a signed transport graph with scalable analyzers.

## Scaling

- Preprocessing, SCC, entropy, residual scoring: `O(V + E)`.
- Signed diffusion / relaxation: `O(iterations * E)`.
- No full cycle enumeration; loop effects are SCC-level holonomy proxies.

## Summary

- nodes: `2825`
- edges: `9578`
- SCCs: `2825` (nontrivial: `0`)
- diffusion iterations: `12` with `alpha=0.2`
- diffusion max delta: `71.9073`
- total entropy production (pairwise): `2.23483e+06`
- total loop harmonic mass proxy: `0`
- total frustrated edges (Wilson proxy): `154`

## Top Chiral Sources

| Node | Potential | Obstruction | Harmonic | Entropy | Boundary |
| --- | --- | --- | --- | --- | --- |
| InfoGeometry.Canonical.MoE.ExpertIdx | 146.09 | 519.39 | 0 | 3733 | internal |
| InfoGeometry.Canonical.DrazinSupercharge.commutator | 47.691 | 308.33 | 0 | 2606.4 | internal |
| InfoGeometry.Canonical.PositiveRayCore.PositiveRay | 41.307 | 1538.2 | 0 | 14969 | internal |
| InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.supercharge | 18.077 | 327.43 | 0 | 3093.5 | internal |
| InfoGeometry.Canonical.ModularKLDivergenceBridge.generalizedKL_activeShapeTerm | 13.389 | 39.265 | 0 | 258.76 | internal |
| InfoGeometry.Canonical.ModularKLDivergenceBridge.generalizedKL_kernelMassTerm | 13.389 | 39.265 | 0 | 258.76 | internal |
| InfoGeometry.Canonical.MoE.unnormalizedWeights | 10.031 | 171.21 | 0 | 1611.8 | internal |
| InfoGeometry.Canonical.MoE.normalizedWeights | 9.4469 | 229.76 | 0 | 2203.1 | internal |
| InfoGeometry.LLM.RouterFreeEnergyBridge.beta_mul_routerFreeEnergy_eq_neg_routerMassieu | 8.1337 | 53.546 | 0 | 454.12 | internal |
| InfoGeometry.Canonical.MoE.routerEnergy | 7.9153 | 165.52 | 0 | 1576 | internal |
| InfoGeometry.Canonical.MoE.routerPartition | 7.4218 | 196.05 | 0 | 1886.3 | internal |
| InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.ZeroModeRegularizationPackage | 6.5226 | 65.825 | 0 | 593.02 | internal |
| InfoGeometry.Canonical.MoE.normalizedMixture | 6.1095 | 105.74 | 0 | 996.33 | internal |
| InfoGeometry.Canonical.SuperchargeCentralChargeClosure.unified_supercharge_central_supergeometry_topological_closure | 5.4 | 366.99 | 0 | 3615.9 | bridge |
| InfoGeometry.Canonical.RealBdGDIIIAtom.canonicalDIIIProxy_transport_root_parity_boundary_kkt_headSuperBracket_closure | 4.9314 | 362.26 | 0 | 3573.3 | bridge |
| InfoGeometry.Canonical.RealBdGDIIIAtom.canonicalDIIIProxy_transport_root_parity_vortexWitness_kkt_headSuperBracket_closure | 4.8 | 339.1 | 0 | 3343 | bridge |
| InfoGeometry.Canonical.RealBdGDIIIAtom.canonicalDIIIProxy_transport_root_parity_boundaryGenerator_kkt_headSuperBracket_closure | 4.7305 | 350.54 | 0 | 3458.1 | bridge |
| InfoGeometry.Canonical.RealBdGDIIIAtom.canonicalDIIIProxy_transport_root_parity_vorticity_kkt_headSuperBracket_closure | 4.5333 | 338.83 | 0 | 3343 | bridge |
| InfoGeometry.Canonical.TopologicalInvariantInvariance.operatorialCentralChargeParity_ne_zero_boundaryScale_kkt_and_headSuperBracket_package_of_identifiedTransportedPolarization | 4.3324 | 319.87 | 0 | 3155.4 | bridge |
| InfoGeometry.Canonical.DrazinSupercharge.canonical_split_with_intrinsic_nonScalar_and_index_shadow | 3.73 | 270.23 | 0 | 2665 | bridge |

## Top Chiral Sinks

| Node | Potential | Obstruction | Harmonic | Entropy | Boundary |
| --- | --- | --- | --- | --- | --- |
| InfoGeometry.KK.RealSplitKreinDiracFredholmModule | -153.12 | 2914.2 | 0 | 27611 | internal |
| InfoGeometry.Clifford.NeutralPhaseSpaceCore.PhaseSpaceCarrier | -85.766 | 2189.2 | 0 | 21035 | internal |
| InfoGeometry.Canonical.RelationalInformationCore.ObservableAlgebra | -76.43 | 496.65 | 0 | 4202.2 | internal |
| InfoGeometry.Canonical.SplitCliffordTensorBridge.SplitClNNTensorStep | -60.021 | 1087.4 | 0 | 10273 | internal |
| InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum | -59.737 | 2512 | 0 | 24522 | internal |
| InfoGeometry.Canonical.ModularSpectralWedge.HasModularSpectralWedge | -51.809 | 617.69 | 0 | 5658.9 | internal |
| InfoGeometry.Canonical.MoE.SinkhornMatrix | -45.634 | 644.31 | 0 | 5986.7 | internal |
| InfoGeometry.Canonical.RelationalInformationCore.RelationalInformationDatum | -34.266 | 844.24 | 0 | 8099.8 | internal |
| InfoGeometry.Canonical.KKTCore.minusProjector | -34.095 | 518.47 | 0 | 4843.8 | internal |
| InfoGeometry.Canonical.KKTCore.plusProjector | -34.093 | 518.47 | 0 | 4843.8 | internal |
| InfoGeometry.Canonical.RelationalInformationDynamics.operatorInformationFirstVariation | -30.783 | 269.89 | 0 | 2391 | internal |
| InfoGeometry.Canonical.GeneralizedMetricCore.tomitaGeneralizedMetricSeed | -24.594 | 498.38 | 0 | 4737.8 | internal |
| InfoGeometry.Canonical.RealTomitaCore.RealModularLogData | -22.21 | 225.4 | 0 | 2031.9 | internal |
| InfoGeometry.Canonical.VortexAnomalyLink.VortexPair | -21.052 | 36.987 | 0 | 159.35 | internal |
| InfoGeometry.Clifford.ClNN.headPair | -19.92 | 305.07 | 0 | 2851.5 | internal |
| InfoGeometry.Canonical.OperatorDictionary.phaseAxisK | -19.059 | 583.67 | 0 | 5646.1 | internal |
| InfoGeometry.LLM.ThermodynamicSwitching.exists_modewiseClifford_rep_of_bistochastic_switch | -17.6 | 88.231 | 0 | 706.31 | mixed |
| InfoGeometry.Canonical.SuperchargeTransportBridge.transportedParitySupercharge | -16.895 | 424.27 | 0 | 4073.7 | internal |
| InfoGeometry.Canonical.SplitCliffordTensorBridge.SplitClNNAlg | -16.416 | 336.11 | 0 | 3196.9 | internal |
| InfoGeometry.Canonical.RelationalInformationCore.PerturbationChannel | -15.332 | 2223.4 | 0 | 22080 | internal |

## Top Non-Equilibrium Pairs (Entropy Production)

| Pair | sigma | rateAB | rateBA | |delta rate| |
| --- | --- | --- | --- | --- |
| InfoGeometry.LLM.AllTopThermodynamicRouter.allTopWeight_eq_finiteGibbs <-> InfoGeometry.LLM.AllTopThermodynamicRouter.allTopWeight_eq_normalizedWeight | 327.07 | 14 | 0 | 14 |
| InfoGeometry.LLM.AllTopThermodynamicRouter.allTopWeight_eq_finiteGibbs <-> InfoGeometry.LLM.RouterFreeEnergyBridge.normalizedWeights_eq_finite_gibbsWeight | 327.07 | 14 | 0 | 14 |
| InfoGeometry.LLM.KMSSoftmaxBridge.softmaxWeight_eq_kmsWeight <-> InfoGeometry.LLM.RouterFreeEnergyBridge.normalizedWeights_eq_finite_gibbsWeight | 327.07 | 14 | 0 | 14 |
| InfoGeometry.Canonical.BoundaryChiralIndexBridge.transportedZeroModeWitness_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization <-> InfoGeometry.Canonical.SpinorModularBridge.exists_danglingZeroMode_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization | 314.9 | 0 | 13.5 | 13.5 |
| InfoGeometry.Canonical.MoE.ExpertIdx <-> InfoGeometry.LLM.AllTopThermodynamicRouter.allTopWeight_eq_finiteGibbs | 314.9 | 0 | 13.5 | 13.5 |
| InfoGeometry.Canonical.MoE.ExpertIdx <-> InfoGeometry.LLM.KMSSoftmaxBridge.softmaxWeight_eq_kmsWeight | 314.9 | 0 | 13.5 | 13.5 |
| InfoGeometry.Canonical.MoE.normalizedWeights <-> InfoGeometry.LLM.AllTopThermodynamicRouter.allTopWeight_eq_finiteGibbs | 314.9 | 0 | 13.5 | 13.5 |
| InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk2.stateFirst_apexZero_activeOnly_operatorialCramerRao <-> InfoGeometry.Canonical.OperatorialCramerRaoStateFirstSemanticAudit.chunk2_active_only_reduction_audit | 314.9 | 0 | 13.5 | 13.5 |
| InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk3.stateFirst_admissibleGate_transport_and_operatorialCramerRao <-> InfoGeometry.Canonical.OperatorialCramerRaoStateFirstSemanticAudit.chunk3_admissibility_base_audit | 314.9 | 0 | 13.5 | 13.5 |
| InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk3.stateFirst_admissibleGate_transport_and_operatorialCramerRao <-> InfoGeometry.Canonical.OperatorialCramerRaoStateFirstSemanticAudit.chunk3_admissibility_compressed_audit | 314.9 | 0 | 13.5 | 13.5 |
| InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk3.stateFirst_admissibleGate_transport_and_operatorialCramerRao <-> InfoGeometry.Canonical.OperatorialCramerRaoStateFirstSemanticAudit.chunk3_admissibility_package_audit | 314.9 | 0 | 13.5 | 13.5 |
| InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk3.stateFirst_admissibleGate_transport_and_operatorialCramerRao <-> InfoGeometry.Canonical.OperatorialCramerRaoStateFirstSemanticAudit.chunk3_cr_lower_bound_audit | 314.9 | 0 | 13.5 | 13.5 |
| InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk4.stateFirst_measurable_uncertainty_operatorialCramerRao_package <-> InfoGeometry.Canonical.OperatorialCramerRaoStateFirstSemanticAudit.chunk4_cr_lower_bound_audit | 314.9 | 0 | 13.5 | 13.5 |
| InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk4.stateFirst_measurable_uncertainty_operatorialCramerRao_package <-> InfoGeometry.Canonical.OperatorialCramerRaoStateFirstSemanticAudit.chunk4_measurable_base_audit | 314.9 | 0 | 13.5 | 13.5 |
| InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk4.stateFirst_measurable_uncertainty_operatorialCramerRao_package <-> InfoGeometry.Canonical.OperatorialCramerRaoStateFirstSemanticAudit.chunk4_measurable_compressed_audit | 314.9 | 0 | 13.5 | 13.5 |
| InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk4.stateFirst_measurable_uncertainty_operatorialCramerRao_package <-> InfoGeometry.Canonical.OperatorialCramerRaoStateFirstSemanticAudit.chunk4_measurable_uncertainty_package_audit | 314.9 | 0 | 13.5 | 13.5 |
| InfoGeometry.Canonical.OperatorialCramerRaoStateFirstChunk4.stateFirst_measurable_uncertainty_operatorialCramerRao_package <-> InfoGeometry.Canonical.OperatorialCramerRaoStateFirstSemanticAudit.chunk4_uncertainty_inequality_audit | 314.9 | 0 | 13.5 | 13.5 |
| InfoGeometry.Canonical.BohmMadelungOperatorialBridge.potentialDatum_constantStateGeneratorField_kSplitReadout_stationary_iff_isPotentialKillingOperator <-> InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum | 302.75 | 13 | 0 | 13 |
| InfoGeometry.Canonical.BohmMadelungOperatorialBridge.potentialDatum_constantStateGeneratorField_stateQGTReadout_pair_eq_comparisonReadout_pair <-> InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum | 302.75 | 13 | 0 | 13 |
| InfoGeometry.Canonical.BohmMadelungOperatorialBridge.potentialDatum_constantStateGeneratorField_stateQGTReadout_stationary_iff_isPotentialKillingOperator <-> InfoGeometry.Canonical.RelativeModularPotential.PotentialDatum | 302.75 | 13 | 0 | 13 |

## Top Loop Obstructions (SCC Holonomy Proxy)

_None._

## Top Wilson Frustration Components (Undirected Signed Proxy)

| Component | nodes | edges | frustrated | frustrationRatio |
| --- | --- | --- | --- | --- |
| 0 | 2640 | 9476 | 154 | 0.016252 |
| 17 | 13 | 18 | 0 | 0 |
| 1 | 9 | 8 | 0 | 0 |
| 19 | 6 | 8 | 0 | 0 |
| 11 | 6 | 5 | 0 | 0 |
| 94 | 5 | 5 | 0 | 0 |
| 4 | 5 | 4 | 0 | 0 |
| 44 | 5 | 4 | 0 | 0 |
| 14 | 4 | 3 | 0 | 0 |
| 22 | 4 | 3 | 0 | 0 |
| 80 | 4 | 3 | 0 | 0 |
| 87 | 4 | 3 | 0 | 0 |
| 92 | 3 | 3 | 0 | 0 |
| 5 | 3 | 2 | 0 | 0 |
| 15 | 3 | 2 | 0 | 0 |
| 33 | 3 | 2 | 0 | 0 |
| 41 | 3 | 2 | 0 | 0 |
| 45 | 3 | 2 | 0 | 0 |
| 47 | 3 | 2 | 0 | 0 |
| 69 | 3 | 2 | 0 | 0 |

## Top Obstruction Corridors (Edges)

| Edge | Score | Residual | Debt | Role | Boundary | Polarity | LoopSCC |
| --- | --- | --- | --- | --- | --- | --- | --- |
| InfoGeometry.Canonical.SuperchargeCentralChargeClosure.unified_supercharge_central_supergeometry_topological_closure -> InfoGeometry.KK.RealSplitKreinDiracFredholmModule | 157.52 | -157.52 | 0 | transportArg | bridge | descending | - |
| InfoGeometry.Canonical.RealBdGDIIIAtom.canonicalDIIIProxy_transport_root_parity_boundary_kkt_headSuperBracket_closure -> InfoGeometry.KK.RealSplitKreinDiracFredholmModule | 157.05 | -157.05 | 0 | transportArg | bridge | descending | - |
| InfoGeometry.Canonical.RealBdGDIIIAtom.canonicalDIIIProxy_transport_root_parity_vortexWitness_kkt_headSuperBracket_closure -> InfoGeometry.KK.RealSplitKreinDiracFredholmModule | 156.92 | -156.92 | 0 | transportArg | bridge | descending | - |
| InfoGeometry.Canonical.RealBdGDIIIAtom.canonicalDIIIProxy_transport_root_parity_boundaryGenerator_kkt_headSuperBracket_closure -> InfoGeometry.KK.RealSplitKreinDiracFredholmModule | 156.85 | -156.85 | 0 | transportArg | bridge | descending | - |
| InfoGeometry.Canonical.RealBdGDIIIAtom.canonicalDIIIProxy_transport_root_parity_vorticity_kkt_headSuperBracket_closure -> InfoGeometry.KK.RealSplitKreinDiracFredholmModule | 156.66 | -156.66 | 0 | transportArg | bridge | descending | - |
| InfoGeometry.Canonical.TopologicalInvariantInvariance.operatorialCentralChargeParity_ne_zero_boundaryScale_kkt_and_headSuperBracket_package_of_identifiedTransportedPolarization -> InfoGeometry.KK.RealSplitKreinDiracFredholmModule | 156.46 | -156.46 | 0 | transportArg | bridge | descending | - |
| InfoGeometry.Canonical.DrazinSupercharge.canonical_split_with_intrinsic_nonScalar_and_index_shadow -> InfoGeometry.KK.RealSplitKreinDiracFredholmModule | 155.85 | -155.85 | 0 | transportArg | bridge | descending | - |
| InfoGeometry.Canonical.RealBdGDIIIAtom.canonicalDIIIProxy_transport_parity_kkt_closure -> InfoGeometry.KK.RealSplitKreinDiracFredholmModule | 155.32 | -155.32 | 0 | transportArg | bridge | descending | - |
| InfoGeometry.Canonical.RealBdGDIIIAtom.canonicalDIIIProxy_transport_root_parity_kkt_closure -> InfoGeometry.KK.RealSplitKreinDiracFredholmModule | 155.32 | -155.32 | 0 | transportArg | bridge | descending | - |
| InfoGeometry.Canonical.TopologicalInvariantInvariance.quasilatticeAnalyticalIndex_ne_zero_sinkBoundaryReadout_package -> InfoGeometry.KK.RealSplitKreinDiracFredholmModule | 155.32 | -155.32 | 0 | transportArg | bridge | descending | - |
| InfoGeometry.Canonical.TopologicalInvariantInvariance.quasilatticeAnalyticalIndex_ne_zero_sinkBoundaryReadout_package_of_kernelSeparation -> InfoGeometry.KK.RealSplitKreinDiracFredholmModule | 155.32 | -155.32 | 0 | transportArg | bridge | descending | - |
| InfoGeometry.Canonical.TopologicalInvariantInvariance.quasilatticeAnalyticalIndex_ne_zero_sourceBoundaryReadout_package -> InfoGeometry.KK.RealSplitKreinDiracFredholmModule | 155.32 | -155.32 | 0 | transportArg | bridge | descending | - |
| InfoGeometry.Canonical.TopologicalInvariantInvariance.quasilatticeAnalyticalIndex_ne_zero_sourceBoundaryReadout_package_of_kernelSeparation -> InfoGeometry.KK.RealSplitKreinDiracFredholmModule | 155.32 | -155.32 | 0 | transportArg | bridge | descending | - |
| InfoGeometry.Canonical.DrazinCentralChargeBridge.DrazinLane.exists_internal_split_with_intrinsic_nonScalar_shadow -> InfoGeometry.KK.RealSplitKreinDiracFredholmModule | 155.26 | -155.26 | 0 | transportArg | bridge | descending | - |
| InfoGeometry.Canonical.SuperchargeCentralChargeClosure.cpt_gap_hessian_centralCharge_with_oscillator_spine -> InfoGeometry.KK.RealSplitKreinDiracFredholmModule | 155.12 | -155.12 | 0 | transportArg | bridge | descending | - |
| InfoGeometry.Canonical.TopologicalInvariantInvariance.operatorialCentralCharge_ne_zero_transportCommutator_and_kkt_packet_of_boundaryGenerator_eq_source_or_sink_of_identifiedTransportedPolarization -> InfoGeometry.KK.RealSplitKreinDiracFredholmModule | 155.12 | -155.12 | 0 | transportArg | bridge | descending | - |
| InfoGeometry.Canonical.SuperchargeCentralChargeClosure.root_central_supercharge_theorem -> InfoGeometry.KK.RealSplitKreinDiracFredholmModule | 155.06 | -155.06 | 0 | transportArg | bridge | descending | - |
| InfoGeometry.Canonical.TopologicalInvariantInvariance.operatorialCentralChargeParity_ne_zero_boundaryScale_and_kkt_package_of_identifiedTransportedPolarization -> InfoGeometry.KK.RealSplitKreinDiracFredholmModule | 155.06 | -155.06 | 0 | transportArg | bridge | descending | - |
| InfoGeometry.Canonical.SuperchargeCentralChargeClosure.cpt_gap_hessian_parity_kkt_closure -> InfoGeometry.KK.RealSplitKreinDiracFredholmModule | 155 | -155 | 0 | transportArg | bridge | descending | - |
| InfoGeometry.Canonical.DrazinCentralChargeBridge.DrazinLane.exists_internal_split_with_intrinsic_nonScalar_shadow_and_witness -> InfoGeometry.KK.RealSplitKreinDiracFredholmModule | 154.92 | -154.92 | 0 | transportArg | bridge | descending | - |
