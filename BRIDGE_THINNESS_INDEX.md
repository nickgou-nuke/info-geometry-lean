# Bridge Thinness Index

Generated: `2026-04-10 00:07:06`

This report is a heuristic audit of bridge-/launchpad-/interface-facing theorem surfaces that may be mathematically thinner than their names suggest.

## Status
- thin-bridge gate: **PASS**
- interpretation: `FAIL` means at least one targeted theorem currently looks like a definitional identity

## Counts
- total tracked findings: **5**
- definitional identity findings: **0**
- direct forwarder findings: **2**
- underscore-hypothesis findings: **3**
- package/orchestration findings: **0**

## Queue
- `medium` `underscore_hypothesis` `moorePenroseRightProjector_ne_one_of_hasZeroMode` at `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:80`
- `medium` `underscore_hypothesis` `moorePenroseLeftProjector_ne_one_of_hasZeroMode` at `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:95`
- `medium` `underscore_hypothesis` `drazinProjection_ne_one_of_hasZeroMode` at `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:109`
- `medium` `direct_forwarder` `bottStep_headNullMinus` at `lean/InfoGeometry/Canonical/ClNNBottBridge.lean:60`
- `medium` `direct_forwarder` `bottStep_headNullPlus` at `lean/InfoGeometry/Canonical/ClNNBottBridge.lean:68`

## Findings
- `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:80` `moorePenroseRightProjector_ne_one_of_hasZeroMode` [medium]
  declaration head contains underscore-prefixed hypotheses: `_hMP`
- `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:95` `moorePenroseLeftProjector_ne_one_of_hasZeroMode` [medium]
  declaration head contains underscore-prefixed hypotheses: `_hMP`
- `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:109` `drazinProjection_ne_one_of_hasZeroMode` [medium]
  declaration head contains underscore-prefixed hypotheses: `_hD`
- `lean/InfoGeometry/Canonical/ClNNBottBridge.lean:60` `bottStep_headNullMinus` [medium]
  proof body is a `simpa ... using bottStep_headPair` forwarder
- `lean/InfoGeometry/Canonical/ClNNBottBridge.lean:68` `bottStep_headNullPlus` [medium]
  proof body is a `simpa ... using bottStep_headPair` forwarder

## Policy
- this is a heuristic syntax audit, not a proof oracle
- `rfl`/direct-forward/package findings are review targets, not automatic verdicts of invalid mathematics
- the purpose is to keep bridge names aligned with actual proof depth
