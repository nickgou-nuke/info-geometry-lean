# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:48.047897+00:00`
Root: `lean/InfoGeometry/Canonical/RealDoubledCliffordFiniteSpine.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **5**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RealDoubledCliffordFiniteSpine.lean` | `advisory` | 11 | 0 | 5 | 1 | 6 |

## Findings by file

### `lean/InfoGeometry/Canonical/RealDoubledCliffordFiniteSpine.lean`
- module: `InfoGeometry.Canonical.RealDoubledCliffordFiniteSpine`
- status: `advisory`
- debt_score: `11`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L83 [soft] `skeletal-proof` in `theorem K_eq_J_comp_epsilon` — proof appears to close via minimal tactic one-liner
  - L96 [soft] `skeletal-proof` in `theorem clock_eq_K` — proof appears to close via minimal tactic one-liner
  - L135 [soft] `skeletal-proof` in `theorem cl11EquivMat_eq_owner` — proof appears to close via minimal tactic one-liner
  - L204 [soft] `skeletal-proof` in `theorem splitBottStep_eq_owner` — proof appears to close via minimal tactic one-liner
  - L224 [soft] `skeletal-proof` in `theorem cl44_as_splitBottStep_eq_owner` — proof appears to close via minimal tactic one-liner

