# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:06.618067+00:00`
Root: `lean/InfoGeometry/Canonical/TopologicalInvariantInvariance.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **15**
- Hard: **0**
- Soft: **6**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/TopologicalInvariantInvariance.lean` | `advisory` | 21 | 0 | 6 | 9 | 15 |

## Findings by file

### `lean/InfoGeometry/Canonical/TopologicalInvariantInvariance.lean`
- module: `InfoGeometry.Canonical.TopologicalInvariantInvariance`
- status: `advisory`
- debt_score: `21`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [soft] `skeletal-proof` in `theorem nullCAR_phaseFlip_invariant` — proof appears to close via minimal tactic one-liner
  - L48 [soft] `skeletal-proof` in `theorem nullMinus_sq_phaseFlip_invariant` — proof appears to close via minimal tactic one-liner
  - L57 [soft] `skeletal-proof` in `theorem nullPlus_sq_phaseFlip_invariant` — proof appears to close via minimal tactic one-liner
  - L80 [soft] `skeletal-proof` in `theorem canonical_wittenIndexResidue_eq_zero` — proof appears to close via minimal tactic one-liner
  - L106 [soft] `skeletal-proof` in `theorem fixedGrading_phaseFlip_projectorSwap` — proof appears to close via minimal tactic one-liner
  - L144 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L152 [soft] `skeletal-proof` in `theorem quasilatticeAnalyticalIndex_transport_invariant` — proof appears to close via minimal tactic one-liner
  - L502 [advisory] `existential-packaging` in `theorem operatorialCentralChargeParity_ne_zero_exists_localizedBoundaryVortex_of_identifiedTransportedPolarization` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L536 [advisory] `existential-packaging` in `theorem operatorialCentralChargeParity_ne_zero_exists_localizedBoundaryVortex_of_kernelSeparation_of_identifiedTransportedPolarization` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L572 [advisory] `existential-packaging` in `theorem quasilatticeAnalyticalIndex_ne_zero_sourceBoundaryReadout_package` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L638 [advisory] `existential-packaging` in `theorem quasilatticeAnalyticalIndex_ne_zero_sinkBoundaryReadout_package` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L893 [advisory] `bridge-shaped-declaration` in `theorem operatorialCentralCharge_ne_zero_transportCommutator_and_kkt_packet_of_boundaryGenerator_eq_source_or_sink_of_identifiedTransportedPolarization` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L946 [advisory] `existential-packaging` in `theorem quasilatticeAnalyticalIndex_ne_zero_sourceBoundaryReadout_package_of_kernelSeparation` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1008 [advisory] `existential-packaging` in `theorem quasilatticeAnalyticalIndex_ne_zero_sinkBoundaryReadout_package_of_kernelSeparation` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

