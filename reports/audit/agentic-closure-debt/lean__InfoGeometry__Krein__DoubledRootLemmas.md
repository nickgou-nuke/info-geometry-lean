# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:50.411529+00:00`
Root: `lean/InfoGeometry/Krein/DoubledRootLemmas.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **4**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Krein/DoubledRootLemmas.lean` | `advisory` | 10 | 0 | 4 | 2 | 6 |

## Findings by file

### `lean/InfoGeometry/Krein/DoubledRootLemmas.lean`
- module: `InfoGeometry.Krein.DoubledRootLemmas`
- status: `advisory`
- debt_score: `10`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L16 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L32 [soft] `skeletal-proof` in `theorem doubledJ_sq` — proof appears to close via minimal tactic one-liner
  - L38 [soft] `skeletal-proof` in `theorem doubledEpsilon_sq` — proof appears to close via minimal tactic one-liner
  - L44 [soft] `skeletal-proof` in `theorem doubledJ_doubledEpsilon_anticommute` — proof appears to close via minimal tactic one-liner
  - L50 [soft] `skeletal-proof` in `theorem doubledI_sq` — proof appears to close via minimal tactic one-liner

