# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:34.192349+00:00`
Root: `lean/InfoGeometry/Canonical/OddDefectFunctional.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **1**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/OddDefectFunctional.lean` | `advisory` | 6 | 0 | 1 | 4 | 5 |

## Findings by file

### `lean/InfoGeometry/Canonical/OddDefectFunctional.lean`
- module: `InfoGeometry.Canonical.OddDefectFunctional`
- status: `advisory`
- debt_score: `6`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L83 [advisory] `existential-packaging` in `theorem projectiveCountDefectBarrier_nonneg` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L211 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L213 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L220 [soft] `skeletal-proof` in `theorem onsager_responseCoefficient_swap` — proof appears to close via minimal tactic one-liner

