# Bridge Thinness Index

Generated: `2026-04-13 02:22:17`

This report is a heuristic audit of bridge-/launchpad-/interface-facing theorem surfaces that may be mathematically thinner than their names suggest.

## Status
- thin-bridge gate: **PASS**
- interpretation: `FAIL` means at least one targeted theorem currently looks like a definitional identity

## Counts
- total tracked findings: **17**
- definitional identity findings: **0**
- direct forwarder findings: **8**
- underscore-hypothesis findings: **4**
- package/orchestration findings: **5**

## Queue
- `medium` `underscore_hypothesis` `moorePenroseRightProjector_ne_one_of_hasZeroMode` at `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:81`
- `medium` `underscore_hypothesis` `moorePenroseLeftProjector_ne_one_of_hasZeroMode` at `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:96`
- `medium` `underscore_hypothesis` `drazinProjection_ne_one_of_hasZeroMode` at `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:110`
- `medium` `direct_forwarder` `bottStep_headNullMinus` at `lean/InfoGeometry/Canonical/ClNNBottBridge.lean:60`
- `medium` `direct_forwarder` `bottStep_headNullPlus` at `lean/InfoGeometry/Canonical/ClNNBottBridge.lean:68`
- `medium` `underscore_hypothesis` `defectProjector_ne_zero_of_package` at `lean/InfoGeometry/Canonical/DrazinFredholmBridge.lean:178`
- `medium` `direct_forwarder` `splitCliffordTensorStep_headFactor` at `lean/InfoGeometry/Canonical/SplitCliffordTensorBridge.lean:148`
- `medium` `direct_forwarder` `splitCliffordTensorStep_tailFactor` at `lean/InfoGeometry/Canonical/SplitCliffordTensorBridge.lean:157`
- `medium` `direct_forwarder` `splitCliffordTensorStep_headNullMinus` at `lean/InfoGeometry/Canonical/SplitCliffordTensorBridge.lean:166`
- `medium` `direct_forwarder` `splitCliffordTensorStep_headNullPlus` at `lean/InfoGeometry/Canonical/SplitCliffordTensorBridge.lean:173`
- `medium` `direct_forwarder` `splitCl44_headFactor` at `lean/InfoGeometry/Canonical/SplitCliffordTensorBridge.lean:203`
- `medium` `direct_forwarder` `splitCl44_tailFactor` at `lean/InfoGeometry/Canonical/SplitCliffordTensorBridge.lean:212`
- `low` `package_orchestration` `exists_canonicalDrazinInverse_global` at `lean/InfoGeometry/Canonical/DrazinExistenceBridge.lean:49`
- `low` `package_orchestration` `harmonic_oscillator_spine` at `lean/InfoGeometry/Canonical/SuperchargeCARCCRBridge.lean:258`
- `low` `package_orchestration` `operatorialCentralChargeParity_ne_zero_boundaryScale_and_kkt_package_of_identifiedTransportedPolarization` at `lean/InfoGeometry/Canonical/TopologicalInvariantInvariance.lean:336`
- `low` `package_orchestration` `operatorialCentralChargeParity_ne_zero_boundaryScale_kkt_and_headSuperBracket_package_of_identifiedTransportedPolarization` at `lean/InfoGeometry/Canonical/TopologicalInvariantInvariance.lean:392`
- `low` `package_orchestration` `comparisonPhaseReadout_sinkVortexSeed_eq_of_sinkSectorDegeneracy` at `lean/InfoGeometry/Canonical/VortexReferenceGaugeBridge.lean:273`

## Findings
- `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:81` `moorePenroseRightProjector_ne_one_of_hasZeroMode` [medium]
  declaration head contains underscore-prefixed hypotheses: `_hMP`
- `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:96` `moorePenroseLeftProjector_ne_one_of_hasZeroMode` [medium]
  declaration head contains underscore-prefixed hypotheses: `_hMP`
- `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:110` `drazinProjection_ne_one_of_hasZeroMode` [medium]
  declaration head contains underscore-prefixed hypotheses: `_hD`
- `lean/InfoGeometry/Canonical/ClNNBottBridge.lean:60` `bottStep_headNullMinus` [medium]
  proof body is a `simpa ... using bottStep_headPair` forwarder
- `lean/InfoGeometry/Canonical/ClNNBottBridge.lean:68` `bottStep_headNullPlus` [medium]
  proof body is a `simpa ... using bottStep_headPair` forwarder
- `lean/InfoGeometry/Canonical/DrazinFredholmBridge.lean:178` `defectProjector_ne_zero_of_package` [medium]
  declaration head contains underscore-prefixed hypotheses: `_hPkg`
- `lean/InfoGeometry/Canonical/SplitCliffordTensorBridge.lean:148` `splitCliffordTensorStep_headFactor` [medium]
  proof body is a `simpa ... using bottStep_headPair` forwarder
- `lean/InfoGeometry/Canonical/SplitCliffordTensorBridge.lean:157` `splitCliffordTensorStep_tailFactor` [medium]
  proof body is a `simpa ... using bottStep_tailLift` forwarder
- `lean/InfoGeometry/Canonical/SplitCliffordTensorBridge.lean:166` `splitCliffordTensorStep_headNullMinus` [medium]
  proof body is a `simpa ... using bottStep_headNullMinus` forwarder
- `lean/InfoGeometry/Canonical/SplitCliffordTensorBridge.lean:173` `splitCliffordTensorStep_headNullPlus` [medium]
  proof body is a `simpa ... using bottStep_headNullPlus` forwarder
- `lean/InfoGeometry/Canonical/SplitCliffordTensorBridge.lean:203` `splitCl44_headFactor` [medium]
  proof body is a `simpa ... using splitCliffordTensorStep_headFactor` forwarder
- `lean/InfoGeometry/Canonical/SplitCliffordTensorBridge.lean:212` `splitCl44_tailFactor` [medium]
  proof body is a `simpa ... using splitCliffordTensorStep_tailFactor` forwarder
- `lean/InfoGeometry/Canonical/DrazinExistenceBridge.lean:49` `exists_canonicalDrazinInverse_global` [low]
  proof body is primarily package/orchestration (`rcases` + tuple assembly)
- `lean/InfoGeometry/Canonical/SuperchargeCARCCRBridge.lean:258` `harmonic_oscillator_spine` [low]
  proof body is primarily package/orchestration (`rcases` + tuple assembly)
- `lean/InfoGeometry/Canonical/TopologicalInvariantInvariance.lean:336` `operatorialCentralChargeParity_ne_zero_boundaryScale_and_kkt_package_of_identifiedTransportedPolarization` [low]
  proof body is primarily package/orchestration (`rcases` + tuple assembly)
- `lean/InfoGeometry/Canonical/TopologicalInvariantInvariance.lean:392` `operatorialCentralChargeParity_ne_zero_boundaryScale_kkt_and_headSuperBracket_package_of_identifiedTransportedPolarization` [low]
  proof body is primarily package/orchestration (`rcases` + tuple assembly)
- `lean/InfoGeometry/Canonical/VortexReferenceGaugeBridge.lean:273` `comparisonPhaseReadout_sinkVortexSeed_eq_of_sinkSectorDegeneracy` [low]
  proof body is primarily package/orchestration (`rcases` + tuple assembly)

## Policy
- this is a heuristic syntax audit, not a proof oracle
- `rfl`/direct-forward/package findings are review targets, not automatic verdicts of invalid mathematics
- the purpose is to keep bridge names aligned with actual proof depth
