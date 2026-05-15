# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:36.382385+00:00`
Root: `lean/InfoGeometry/Canonical/OperatorLightconeCoordinates.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **3**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/OperatorLightconeCoordinates.lean` | `advisory` | 11 | 0 | 3 | 5 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/OperatorLightconeCoordinates.lean`
- module: `InfoGeometry.Canonical.OperatorLightconeCoordinates`
- status: `advisory`
- debt_score: `11`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L29 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L31 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L32 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L33 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L63 [soft] `skeletal-proof` in `theorem lightconeCoordinate_sum_eq_id_expectation` — proof appears to close via minimal tactic one-liner
  - L103 [soft] `skeletal-proof` in `theorem rapidityPlusCoordinate_eq_exp_mul_lightconePlus` — proof appears to close via minimal tactic one-liner
  - L110 [soft] `skeletal-proof` in `theorem rapidityMinusCoordinate_eq_exp_neg_mul_lightconeMinus` — proof appears to close via minimal tactic one-liner

