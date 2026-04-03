# Bridge Thinness Index

Generated: `2026-04-01 21:12:43`

This report is a heuristic audit of bridge-/launchpad-/interface-facing theorem surfaces that may be mathematically thinner than their names suggest.

## Status
- thin-bridge gate: **PASS**
- interpretation: `FAIL` means at least one targeted theorem currently looks like a definitional identity

## Counts
- total tracked findings: **1**
- definitional identity findings: **0**
- direct forwarder findings: **1**
- underscore-hypothesis findings: **0**
- package/orchestration findings: **0**

## Queue
- `medium` `direct_forwarder` `countRelativeVolumeChange_pos` at `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean:463`

## Findings
- `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean:463` `countRelativeVolumeChange_pos` [medium]
  proof body forwards directly via `exact div_pos`

## Policy
- this is a heuristic syntax audit, not a proof oracle
- `rfl`/direct-forward/package findings are review targets, not automatic verdicts of invalid mathematics
- the purpose is to keep bridge names aligned with actual proof depth
