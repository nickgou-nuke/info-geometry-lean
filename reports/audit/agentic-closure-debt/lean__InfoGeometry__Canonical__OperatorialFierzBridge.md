# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:38.967397+00:00`
Root: `lean/InfoGeometry/Canonical/OperatorialFierzBridge.lean`
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
| `lean/InfoGeometry/Canonical/OperatorialFierzBridge.lean` | `advisory` | 9 | 0 | 3 | 3 | 6 |

## Findings by file

### `lean/InfoGeometry/Canonical/OperatorialFierzBridge.lean`
- module: `InfoGeometry.Canonical.OperatorialFierzBridge`
- status: `advisory`
- debt_score: `9`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L29 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L31 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L69 [soft] `skeletal-proof` in `theorem transportEvaluatedFierzReadout_eq_doubledFierzReadout` — proof appears to close via minimal tactic one-liner
  - L73 [soft] `skeletal-proof` in `theorem operatorTransportScalarReadout_eq_doubledFierz_scalar` — proof appears to close via minimal tactic one-liner
  - L78 [soft] `skeletal-proof` in `theorem operatorTransportAreaReadout_eq_doubledFierz_area` — proof appears to close via minimal tactic one-liner

