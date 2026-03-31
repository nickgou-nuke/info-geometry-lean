# Bridge Thinness Index

Generated: `2026-03-31 18:57:51`

This report is a heuristic audit of bridge-/launchpad-/interface-facing theorem surfaces that may be mathematically thinner than their names suggest.

## Status
- thin-bridge gate: **FAIL**
- interpretation: `FAIL` means at least one targeted theorem currently looks like a definitional identity

## Counts
- total tracked findings: **11**
- definitional identity findings: **9**
- direct forwarder findings: **2**
- underscore-hypothesis findings: **0**
- package/orchestration findings: **0**

## Queue
- `high` `definitional_identity` `rawCountDelta_eq_relativeCountDensity` at `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean:69`
- `high` `definitional_identity` `rawCountLogDelta_eq_relativeCountLogDensity` at `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean:73`
- `high` `definitional_identity` `rawCountHamiltonianProfile_eq_relativeCountModularProfile` at `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean:77`
- `high` `definitional_identity` `rawCountLogDelta_eq_log_rawCountDelta` at `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean:81`
- `high` `definitional_identity` `rawCountHamiltonianProfile_eq_neg_log_rawCountDelta` at `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean:85`
- `high` `definitional_identity` `relativeCountLogDensity_eq_log_relativeCountDensity` at `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean:89`
- `high` `definitional_identity` `relativeCountModularProfile_eq_neg_relativeCountLogDensity` at `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean:94`
- `high` `definitional_identity` `countMassShift_eq_log_massRatio` at `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean:344`
- `high` `definitional_identity` `projectiveCountHamiltonianProfile_eq_projectiveCountModularProfile` at `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean:636`
- `medium` `direct_forwarder` `relativeLogDensityMean_mul` at `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean:267`
- `medium` `direct_forwarder` `countRelativeVolumeChange_pos` at `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean:519`

## Findings
- `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean:69` `rawCountDelta_eq_relativeCountDensity` [high]
  proof body reduces directly to `rfl`
- `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean:73` `rawCountLogDelta_eq_relativeCountLogDensity` [high]
  proof body reduces directly to `rfl`
- `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean:77` `rawCountHamiltonianProfile_eq_relativeCountModularProfile` [high]
  proof body reduces directly to `rfl`
- `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean:81` `rawCountLogDelta_eq_log_rawCountDelta` [high]
  proof body reduces directly to `rfl`
- `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean:85` `rawCountHamiltonianProfile_eq_neg_log_rawCountDelta` [high]
  proof body reduces directly to `rfl`
- `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean:89` `relativeCountLogDensity_eq_log_relativeCountDensity` [high]
  proof body reduces directly to `rfl`
- `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean:94` `relativeCountModularProfile_eq_neg_relativeCountLogDensity` [high]
  proof body reduces directly to `rfl`
- `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean:344` `countMassShift_eq_log_massRatio` [high]
  proof body reduces directly to `rfl`
- `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean:636` `projectiveCountHamiltonianProfile_eq_projectiveCountModularProfile` [high]
  proof body reduces directly to `rfl`
- `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean:267` `relativeLogDensityMean_mul` [medium]
  proof body is a `simpa ... using meanLogDeltaProfile_mul` forwarder
- `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean:519` `countRelativeVolumeChange_pos` [medium]
  proof body forwards directly via `exact div_pos`

## Policy
- this is a heuristic syntax audit, not a proof oracle
- `rfl`/direct-forward/package findings are review targets, not automatic verdicts of invalid mathematics
- the purpose is to keep bridge names aligned with actual proof depth
