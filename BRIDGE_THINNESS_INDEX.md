# Bridge Thinness Index

Generated: `2026-03-20 14:57:58`

This report is a heuristic audit of bridge-/launchpad-/interface-facing theorem surfaces that may be mathematically thinner than their names suggest.

## Status
- thin-bridge gate: **FAIL**
- interpretation: `FAIL` means at least one targeted theorem currently looks like a definitional identity

## Counts
- total tracked findings: **29**
- definitional identity findings: **3**
- direct forwarder findings: **15**
- underscore-hypothesis findings: **2**
- package/orchestration findings: **9**

## Queue
- `high` `definitional_identity` `B_agrees_with_Gauge_bilinear` at `lean/InfoGeometry/Canonical/CliffordBridge.lean:20`
- `high` `definitional_identity` `relative_volume_change_rn_eq_exp_neg_kahler` at `lean/InfoGeometry/Canonical/DiracRicciBridge.lean:37`
- `high` `definitional_identity` `kkt_perelman_correspondence` at `lean/InfoGeometry/Unstable/SingularUnitaryBridge.lean:41`
- `medium` `direct_forwarder` `isRicciFlat_of_unitRelativeVolume_metricDerived` at `lean/InfoGeometry/Canonical/CalabiYauBridge.lean:140`
- `medium` `direct_forwarder` `ricciTensor_unique_of_mongeAmpereRicciState` at `lean/InfoGeometry/Canonical/CalabiYauBridge.lean:232`
- `medium` `direct_forwarder` `isRicciFlat_of_unitRelativeVolume` at `lean/InfoGeometry/Canonical/CalabiYauBridge.lean:258`
- `medium` `direct_forwarder` `vacuumEinsteinEquation_of_unitRelativeVolume` at `lean/InfoGeometry/Canonical/CalabiYauBridge.lean:270`
- `medium` `direct_forwarder` `vacuumEinsteinEquation_of_mongeAmpereRicciState` at `lean/InfoGeometry/Canonical/CalabiYauBridge.lean:284`
- `medium` `direct_forwarder` `cayleyPythagoreanInvariance` at `lean/InfoGeometry/Canonical/CayleyBregmanBridge.lean:98`
- `medium` `direct_forwarder` `countInducedCoupling_hasPositiveRowSums` at `lean/InfoGeometry/Canonical/CountSubstrateBridge.lean:298`
- `medium` `direct_forwarder` `countInducedCoupling_hasPositiveColSums` at `lean/InfoGeometry/Canonical/CountSubstrateBridge.lean:304`
- `medium` `direct_forwarder` `jordan_kkt_barrier_eq_neg_log_det` at `lean/InfoGeometry/Canonical/DiracRicciBridge.lean:86`
- `medium` `direct_forwarder` `log_det_barrier_eq_neg_log_det'` at `lean/InfoGeometry/Canonical/DiracRicciBridge.lean:104`
- `medium` `direct_forwarder` `free_energy_from_log_det_eq_neg_scale_log_partition'` at `lean/InfoGeometry/Canonical/DiracRicciBridge.lean:122`
- `medium` `direct_forwarder` `IBPartitionFunction_shift_eq_smul` at `lean/InfoGeometry/Canonical/IBGaugeBridge.lean:87`
- `medium` `direct_forwarder` `sinkhorn_step_kmsClosure_of_control` at `lean/InfoGeometry/Canonical/KMSSinkhornBridge.lean:177`
- `medium` `underscore_hypothesis` `bayesian_update_as_spinor_bilinear` at `lean/InfoGeometry/Canonical/ModularSpinorBridge.lean:216`
- `medium` `direct_forwarder` `hohenbergKohnDualState_of_concreteLegendre` at `lean/InfoGeometry/Canonical/QFTTDFTLaunchpad.lean:206`
- `medium` `direct_forwarder` `rungeGrossStationaryDualState_of_stationaryAtScale` at `lean/InfoGeometry/Canonical/QFTTDFTLaunchpad.lean:265`
- `medium` `underscore_hypothesis` `index_bridge_spectral` at `lean/InfoGeometry/KK/KasparovCycle.lean:83`
- `low` `package_orchestration` `aqft_readiness_package_with_projectorSuperPair_base` at `lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean:404`
- `low` `package_orchestration` `aqft_tdft_constructive_launchpad_packaged_with_aqft_readiness` at `lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean:458`
- `low` `package_orchestration` `aqft_tdft_constructive_launchpad_with_bogoliubov_projector_superalgebra_packaged_with_aqft_readiness` at `lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean:515`
- `low` `package_orchestration` `aqft_tdft_constructive_launchpad_packaged_with_aqft_readiness_and_projectorSuperPair_base` at `lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean:580`
- `low` `package_orchestration` `realHilbertCompressionInterpretation_packaged_with_aqft_readiness_and_projectorSuperPair_base` at `lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean:686`
- `low` `package_orchestration` `satisfiesMongeAmpere_const_of_hasConstantMongeAmpereDensity` at `lean/InfoGeometry/Canonical/CalabiYauBridge.lean:62`
- `low` `package_orchestration` `cstar_completeCStar_kms_fock_bogoliubov_projector_package` at `lean/InfoGeometry/Canonical/OperatorAlgebraBridge.lean:133`
- `low` `package_orchestration` `cstar_completeCStar_kms_fock_projectorSuperPair_base_package` at `lean/InfoGeometry/Canonical/OperatorAlgebraBridge.lean:181`
- `low` `package_orchestration` `aqft_tdft_constructive_launchpad_with_bogoliubov_projector_superalgebra` at `lean/InfoGeometry/Canonical/QFTTDFTLaunchpad.lean:424`

## Findings
- `lean/InfoGeometry/Canonical/CliffordBridge.lean:20` `B_agrees_with_Gauge_bilinear` [high]
  proof body reduces directly to `rfl`
- `lean/InfoGeometry/Canonical/DiracRicciBridge.lean:37` `relative_volume_change_rn_eq_exp_neg_kahler` [high]
  proof body reduces directly to `rfl`
- `lean/InfoGeometry/Unstable/SingularUnitaryBridge.lean:41` `kkt_perelman_correspondence` [high]
  proof body reduces directly to `rfl`
- `lean/InfoGeometry/Canonical/CalabiYauBridge.lean:140` `isRicciFlat_of_unitRelativeVolume_metricDerived` [medium]
  proof body forwards directly via `exact isRicciFlat_of_isEinsteinKaehlerAtWith_zero`
- `lean/InfoGeometry/Canonical/CalabiYauBridge.lean:232` `ricciTensor_unique_of_mongeAmpereRicciState` [medium]
  proof body forwards directly via `exact ricciTensor_eq_of_isRicciFlat`
- `lean/InfoGeometry/Canonical/CalabiYauBridge.lean:258` `isRicciFlat_of_unitRelativeVolume` [medium]
  proof body forwards directly via `exact isRicciFlat_of_isEinsteinKaehlerAtWith_zero`
- `lean/InfoGeometry/Canonical/CalabiYauBridge.lean:270` `vacuumEinsteinEquation_of_unitRelativeVolume` [medium]
  proof body forwards directly via `exact vacuumEinsteinEquation_of_isRicciFlat`
- `lean/InfoGeometry/Canonical/CalabiYauBridge.lean:284` `vacuumEinsteinEquation_of_mongeAmpereRicciState` [medium]
  proof body forwards directly via `exact vacuumEinsteinEquation_of_isRicciFlat`
- `lean/InfoGeometry/Canonical/CayleyBregmanBridge.lean:98` `cayleyPythagoreanInvariance` [medium]
  proof body is a `simpa ... using cayley_pythagorean_invariance` forwarder
- `lean/InfoGeometry/Canonical/CountSubstrateBridge.lean:298` `countInducedCoupling_hasPositiveRowSums` [medium]
  proof body forwards directly via `exact entrywisePositive_hasPositiveRowSums`
- `lean/InfoGeometry/Canonical/CountSubstrateBridge.lean:304` `countInducedCoupling_hasPositiveColSums` [medium]
  proof body forwards directly via `exact entrywisePositive_hasPositiveColSums`
- `lean/InfoGeometry/Canonical/DiracRicciBridge.lean:86` `jordan_kkt_barrier_eq_neg_log_det` [medium]
  proof body forwards directly via `exact JordanKKTData.K_def`
- `lean/InfoGeometry/Canonical/DiracRicciBridge.lean:104` `log_det_barrier_eq_neg_log_det'` [medium]
  proof body forwards directly via `exact logDetBarrier_eq_neg_log_det`
- `lean/InfoGeometry/Canonical/DiracRicciBridge.lean:122` `free_energy_from_log_det_eq_neg_scale_log_partition'` [medium]
  proof body forwards directly via `exact freeEnergyFromLogDet_eq_neg_scale_log_partition`
- `lean/InfoGeometry/Canonical/IBGaugeBridge.lean:87` `IBPartitionFunction_shift_eq_smul` [medium]
  proof body is a `simpa ... using congrArg` forwarder
- `lean/InfoGeometry/Canonical/KMSSinkhornBridge.lean:177` `sinkhorn_step_kmsClosure_of_control` [medium]
  proof body forwards directly via `exact sinkhorn_step_kmsClosure_of_approxClosure_of_barrierZero`
- `lean/InfoGeometry/Canonical/ModularSpinorBridge.lean:216` `bayesian_update_as_spinor_bilinear` [medium]
  declaration head contains underscore-prefixed hypotheses: `_innovation`
- `lean/InfoGeometry/Canonical/QFTTDFTLaunchpad.lean:206` `hohenbergKohnDualState_of_concreteLegendre` [medium]
  proof body forwards directly via `exact hohenbergKohnDualState_of_inverse_maps`
- `lean/InfoGeometry/Canonical/QFTTDFTLaunchpad.lean:265` `rungeGrossStationaryDualState_of_stationaryAtScale` [medium]
  proof body forwards directly via `exact hStationary.2`
- `lean/InfoGeometry/KK/KasparovCycle.lean:83` `index_bridge_spectral` [medium]
  declaration head contains underscore-prefixed hypotheses: `_hF`
- `lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean:404` `aqft_readiness_package_with_projectorSuperPair_base` [low]
  proof body is primarily package/orchestration (`rcases` + tuple assembly)
- `lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean:458` `aqft_tdft_constructive_launchpad_packaged_with_aqft_readiness` [low]
  proof body is primarily package/orchestration (`rcases` + tuple assembly)
- `lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean:515` `aqft_tdft_constructive_launchpad_with_bogoliubov_projector_superalgebra_packaged_with_aqft_readiness` [low]
  proof body is primarily package/orchestration (`rcases` + tuple assembly)
- `lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean:580` `aqft_tdft_constructive_launchpad_packaged_with_aqft_readiness_and_projectorSuperPair_base` [low]
  proof body is primarily package/orchestration (`rcases` + tuple assembly)
- `lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean:686` `realHilbertCompressionInterpretation_packaged_with_aqft_readiness_and_projectorSuperPair_base` [low]
  proof body is primarily package/orchestration (`rcases` + tuple assembly)
- `lean/InfoGeometry/Canonical/CalabiYauBridge.lean:62` `satisfiesMongeAmpere_const_of_hasConstantMongeAmpereDensity` [low]
  proof body is primarily package/orchestration (`rcases` + tuple assembly)
- `lean/InfoGeometry/Canonical/OperatorAlgebraBridge.lean:133` `cstar_completeCStar_kms_fock_bogoliubov_projector_package` [low]
  proof body is primarily package/orchestration (`rcases` + tuple assembly)
- `lean/InfoGeometry/Canonical/OperatorAlgebraBridge.lean:181` `cstar_completeCStar_kms_fock_projectorSuperPair_base_package` [low]
  proof body is primarily package/orchestration (`rcases` + tuple assembly)
- `lean/InfoGeometry/Canonical/QFTTDFTLaunchpad.lean:424` `aqft_tdft_constructive_launchpad_with_bogoliubov_projector_superalgebra` [low]
  proof body is primarily package/orchestration (`rcases` + tuple assembly)

## Policy
- this is a heuristic syntax audit, not a proof oracle
- `rfl`/direct-forward/package findings are review targets, not automatic verdicts of invalid mathematics
- the purpose is to keep bridge names aligned with actual proof depth
