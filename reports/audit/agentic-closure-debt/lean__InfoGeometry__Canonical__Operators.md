# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:39.932165+00:00`
Root: `lean/InfoGeometry/Canonical/Operators.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **3**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/Operators.lean` | `advisory` | 9 | 0 | 3 | 3 | 6 |

## Findings by file

### `lean/InfoGeometry/Canonical/Operators.lean`
- module: `InfoGeometry.Canonical.Operators`
- status: `advisory`
- debt_score: `9`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L33 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L35 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L91 [soft] `skeletal-proof` in `theorem probedFisherReadout_eq_metricHessianForm` — proof appears to close via minimal tactic one-liner
  - L97 [soft] `skeletal-proof` in `theorem onsagerCoefficient_eq_probedFisherReadout` — proof appears to close via minimal tactic one-liner
  - L109 [soft] `skeletal-proof` in `theorem entropyProduction_eq_probe_hessian` — proof appears to close via minimal tactic one-liner

