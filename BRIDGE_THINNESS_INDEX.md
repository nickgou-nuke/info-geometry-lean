# Bridge Thinness Index

Generated: `2026-04-25 01:28:03`

This report flags bridge-facing theorem surfaces only when syntax-thin proofs also sit on weak DAG graph roles.

## Status
- thin-bridge gate: **PASS**
- interpretation: `FAIL` means at least one targeted theorem looks definitional and is graph-thin/isolated

## Counts
- total tracked findings: **38**
- definitional identity findings: **0**
- direct forwarder findings: **29**
- underscore-hypothesis findings: **5**
- package/orchestration findings: **4**

## Queue
- `medium` `direct_forwarder` `probe_apply_eq_referenceExpectation` at `lean/InfoGeometry/Canonical/AlgebraicStateFunctionalBridge.lean:129` role=`isolated_theorem` theorem_users=0
- `medium` `direct_forwarder` `withFrame_probe_apply_eq_referenceExpectation` at `lean/InfoGeometry/Canonical/AlgebraicStateFunctionalBridge.lean:155` role=`isolated_theorem` theorem_users=0
- `medium` `direct_forwarder` `canopy_unitRelativeVolumeState` at `lean/InfoGeometry/Canonical/CalabiYauBridge.lean:37` role=`graph_unknown` theorem_users=0
- `medium` `direct_forwarder` `canopy_isRicciFlat_and_vacuumEinstein` at `lean/InfoGeometry/Canonical/CalabiYauBridge.lean:52` role=`graph_unknown` theorem_users=0
- `medium` `direct_forwarder` `exists_drazinInverse_of_constructiveClosure` at `lean/InfoGeometry/Canonical/ClosureDrazinBridge.lean:182` role=`isolated_theorem` theorem_users=0
- `medium` `underscore_hypothesis` `defectProjector_ne_zero_of_package` at `lean/InfoGeometry/Canonical/DrazinFredholmBridge.lean:177` role=`isolated_theorem` theorem_users=0
- `medium` `underscore_hypothesis` `exists_drazinInverse_of_zeroIsolatedInSpectrum_package` at `lean/InfoGeometry/Canonical/DrazinSpectralBridge.lean:138` role=`isolated_theorem` theorem_users=0
- `medium` `direct_forwarder` `exists_drazinInverse_of_zeroIsolatedInSpectrum_package` at `lean/InfoGeometry/Canonical/DrazinSpectralBridge.lean:138` role=`isolated_theorem` theorem_users=0
- `medium` `underscore_hypothesis` `exists_drazinInverse_with_projector_split_of_zeroIsolatedInSpectrum_package` at `lean/InfoGeometry/Canonical/DrazinSpectralProjectorBridge.lean:64` role=`isolated_theorem` theorem_users=0
- `medium` `direct_forwarder` `exists_drazinInverse_with_projector_split_of_zeroIsolatedInSpectrum_package` at `lean/InfoGeometry/Canonical/DrazinSpectralProjectorBridge.lean:64` role=`isolated_theorem` theorem_users=0
- `medium` `underscore_hypothesis` `exists_drazin_projection_idempotent_of_zeroIsolatedInSpectrum_package` at `lean/InfoGeometry/Canonical/DrazinSpectralProjectorBridge.lean:92` role=`isolated_theorem` theorem_users=0
- `medium` `direct_forwarder` `chemicalPotential_conjugate_count_readout` at `lean/InfoGeometry/Canonical/GrandCanonicalGaugePotentialBridge.lean:106` role=`isolated_theorem` theorem_users=0
- `medium` `direct_forwarder` `inverseTemperature_conjugate_shiftedEnergy_readout` at `lean/InfoGeometry/Canonical/GrandCanonicalGaugePotentialBridge.lean:119` role=`isolated_theorem` theorem_users=0
- `medium` `direct_forwarder` `absDet_cramerRaoMetric_eq_one_of_incompressibleBit` at `lean/InfoGeometry/Canonical/IncompressibleBitBridge.lean:163` role=`isolated_theorem` theorem_users=0
- `medium` `direct_forwarder` `onsager_phaseChannel_signFlip` at `lean/InfoGeometry/Canonical/MajoranaLiftPacketBridge.lean:105` role=`isolated_theorem` theorem_users=0
- `medium` `direct_forwarder` `relativeModular_scaleShapeSplit_bridge_of_commute` at `lean/InfoGeometry/Canonical/SingularDecompositionSurrogate.lean:296` role=`isolated_theorem` theorem_users=0
- `medium` `direct_forwarder` `cp003_singular_polar_kan_package_of_commute` at `lean/InfoGeometry/Canonical/SingularDecompositionSurrogate.lean:349` role=`isolated_theorem` theorem_users=0
- `medium` `direct_forwarder` `coneAdmissible_of_square` at `lean/InfoGeometry/Canonical/SouriauLieThermoKKTBridge.lean:118` role=`isolated_theorem` theorem_users=0
- `medium` `direct_forwarder` `partitionAdmissible_of_square` at `lean/InfoGeometry/Canonical/SouriauLieThermoKKTBridge.lean:125` role=`isolated_theorem` theorem_users=0
- `medium` `direct_forwarder` `hodgeStarSelfDualSplitOfIncidentNullSeparation_incidenceCompatible` at `lean/InfoGeometry/Canonical/TwistorHodgePalatialBridge.lean:221` role=`isolated_theorem` theorem_users=0
- `medium` `direct_forwarder` `softmaxWeight_eq_kmsWeight` at `lean/InfoGeometry/LLM/KMSSoftmaxBridge.lean:36` role=`isolated_theorem` theorem_users=0
- `medium` `direct_forwarder` `switchMatrix_mem_rowStochastic_bridge` at `lean/InfoGeometry/LLM/ScalarThermoBridge.lean:126` role=`isolated_theorem` theorem_users=0
- `medium` `direct_forwarder` `fenchelGap_nonneg_bridge` at `lean/InfoGeometry/LLM/ScalarThermoBridge.lean:139` role=`isolated_theorem` theorem_users=0
- `medium` `direct_forwarder` `ownerTranslationCandidate_in_dissipativeRange` at `lean/InfoGeometry/SuperMetriplectic/DrazinCartanShadowBridge.lean:91` role=`isolated_theorem` theorem_users=0
- `medium` `direct_forwarder` `hiddenBlock_projectorMismatch_eq_zero_iff` at `lean/InfoGeometry/SuperMetriplectic/EntropyShadowBridge.lean:29` role=`isolated_theorem` theorem_users=0
- `medium` `direct_forwarder` `toChiralSuperchargeClosure_translationReadout_eq_effectiveEvenOnsager` at `lean/InfoGeometry/SuperMetriplectic/TriadBridge.lean:90` role=`isolated_theorem` theorem_users=0
- `medium` `direct_forwarder` `toChiralSuperchargeClosure_defectReadout_eq_drazinDefectProjector` at `lean/InfoGeometry/SuperMetriplectic/TriadBridge.lean:101` role=`isolated_theorem` theorem_users=0
- `medium` `direct_forwarder` `chiralClosureOfTriadOddData_translationReadout_eq_effectiveEvenOnsager` at `lean/InfoGeometry/SuperMetriplectic/TriadBridge.lean:141` role=`isolated_theorem` theorem_users=0
- `medium` `direct_forwarder` `chiralClosureOfTriadOddData_defectReadout_eq_drazinDefectProjector` at `lean/InfoGeometry/SuperMetriplectic/TriadBridge.lean:167` role=`isolated_theorem` theorem_users=0
- `medium` `direct_forwarder` `hiddenBlock_hasMoorePenroseShadow` at `lean/InfoGeometry/SuperMetriplectic/TriadBridge.lean:262` role=`isolated_theorem` theorem_users=0
- `medium` `direct_forwarder` `hiddenBlock_hasDrazinShadow` at `lean/InfoGeometry/SuperMetriplectic/TriadBridge.lean:268` role=`isolated_theorem` theorem_users=0
- `medium` `direct_forwarder` `toCoadjointLeafEntropySplit_totalEntropyChange_eq_entropyProduction` at `lean/InfoGeometry/SuperMetriplectic/TriadBridge.lean:287` role=`isolated_theorem` theorem_users=0
- `medium` `direct_forwarder` `effective_metric_is_schur_complement` at `lean/InfoGeometry/SuperMetriplectic/TriadBridge.lean:332` role=`isolated_theorem` theorem_users=0
- `medium` `underscore_hypothesis` `twistor_incidence_variety` at `lean/InfoGeometry/Twistor/LightconeBridge.lean:54` role=`isolated_theorem` theorem_users=0
- `low` `package_orchestration` `exists_drazin_projection_idempotent_of_zeroIsolatedInSpectrum_package` at `lean/InfoGeometry/Canonical/DrazinSpectralProjectorBridge.lean:92` role=`isolated_theorem` theorem_users=0
- `low` `package_orchestration` `relativeModular_scaleShapeSplit_eq_projectiveGaugeSplit` at `lean/InfoGeometry/Canonical/ModularKLDivergenceBridge.lean:254` role=`graph_unknown` theorem_users=0
- `low` `package_orchestration` `operatorialCentralChargeParity_ne_zero_boundaryScale_and_kkt_package_of_identifiedTransportedPolarization` at `lean/InfoGeometry/Canonical/TopologicalInvariantInvariance.lean:342` role=`graph_unknown` theorem_users=0
- `low` `package_orchestration` `comparisonPhaseReadout_sinkVortexSeed_eq_of_sinkSectorDegeneracy` at `lean/InfoGeometry/Canonical/VortexReferenceGaugeBridge.lean:273` role=`isolated_theorem` theorem_users=0

## Policy
- this is a graph-gated syntax audit, not a proof oracle
- short proofs only enter the queue when the declaration is also graph-thin
- load-bearing bridges are not demoted merely for having concise proofs
