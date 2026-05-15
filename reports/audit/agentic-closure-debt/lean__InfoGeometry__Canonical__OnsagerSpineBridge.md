# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:34.758555+00:00`
Root: `lean/InfoGeometry/Canonical/OnsagerSpineBridge.lean`
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
| `lean/InfoGeometry/Canonical/OnsagerSpineBridge.lean` | `advisory` | 12 | 0 | 4 | 4 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/OnsagerSpineBridge.lean`
- module: `InfoGeometry.Canonical.OnsagerSpineBridge`
- status: `advisory`
- debt_score: `12`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L22 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L24 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L25 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L57 [soft] `skeletal-proof` in `theorem responseCoefficient_eq_spineRespond` — proof appears to close via minimal tactic one-liner
  - L75 [soft] `skeletal-proof` in `theorem curvatureCoefficient_eq_spineRespond` — proof appears to close via minimal tactic one-liner
  - L93 [soft] `skeletal-proof` in `theorem spineRespond_metric_swap` — proof appears to close via minimal tactic one-liner
  - L114 [soft] `skeletal-proof` in `theorem spineRespond_curvature_swap_neg` — proof appears to close via minimal tactic one-liner

