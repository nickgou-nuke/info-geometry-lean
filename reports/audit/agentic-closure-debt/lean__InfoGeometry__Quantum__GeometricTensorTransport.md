# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:34.816037+00:00`
Root: `lean/InfoGeometry/Quantum/GeometricTensorTransport.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **4**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Quantum/GeometricTensorTransport.lean` | `advisory` | 12 | 0 | 4 | 4 | 8 |

## Findings by file

### `lean/InfoGeometry/Quantum/GeometricTensorTransport.lean`
- module: `InfoGeometry.Quantum.GeometricTensorTransport`
- status: `advisory`
- debt_score: `12`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L17 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L19 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L46 [advisory] `local-hypothesis-injection` in `theorem KRotation_preserves_inner` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L132 [soft] `skeletal-proof` in `theorem metricOfOperator_KRotation_eq_of_commute` — proof appears to close via minimal tactic one-liner
  - L159 [soft] `skeletal-proof` in `theorem berryOfOperator_KRotation_eq_of_commute` — proof appears to close via minimal tactic one-liner
  - L330 [soft] `skeletal-proof` in `theorem berryOfOperator_modularTransportFlow_eq_of_commute_generator` — proof appears to close via minimal tactic one-liner
  - L616 [soft] `skeletal-proof` in `theorem kreinMetricOfOperator_KRotation_eq_of_IsPhaseAntilinear` — proof appears to close via minimal tactic one-liner

