# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:18.937456+00:00`
Root: `lean/InfoGeometry/Clifford/RealDoubledHestenesAnchor.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **3**
- Hard: **0**
- Soft: **1**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Clifford/RealDoubledHestenesAnchor.lean` | `advisory` | 4 | 0 | 1 | 2 | 3 |

## Findings by file

### `lean/InfoGeometry/Clifford/RealDoubledHestenesAnchor.lean`
- module: `InfoGeometry.Clifford.RealDoubledHestenesAnchor`
- status: `advisory`
- debt_score: `4`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L18 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L47 [soft] `skeletal-proof` in `theorem hestenes_pseudoscalar_rep_eq_doubledEpsilon` — proof appears to close via minimal tactic one-liner

