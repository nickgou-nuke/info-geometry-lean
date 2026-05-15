# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:45.195053+00:00`
Root: `lean/InfoGeometry/Canonical/BoundaryChiralIndexBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **3**
- Hard: **0**
- Soft: **0**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/BoundaryChiralIndexBridge.lean` | `advisory` | 3 | 0 | 0 | 3 | 3 |

## Findings by file

### `lean/InfoGeometry/Canonical/BoundaryChiralIndexBridge.lean`
- module: `InfoGeometry.Canonical.BoundaryChiralIndexBridge`
- status: `advisory`
- debt_score: `3`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L44 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L141 [advisory] `existential-packaging` in `theorem transportedZeroModeWitness_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

