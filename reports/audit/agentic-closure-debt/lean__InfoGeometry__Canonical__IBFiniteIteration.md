# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:16.991755+00:00`
Root: `lean/InfoGeometry/Canonical/IBFiniteIteration.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **4**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/IBFiniteIteration.lean` | `advisory` | 9 | 0 | 4 | 1 | 5 |

## Findings by file

### `lean/InfoGeometry/Canonical/IBFiniteIteration.lean`
- module: `InfoGeometry.Canonical.IBFiniteIteration`
- status: `advisory`
- debt_score: `9`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L23 [soft] `skeletal-proof` in `theorem ibTrajectory_step_gap_eq_zero` — proof appears to close via minimal tactic one-liner
  - L39 [soft] `skeletal-proof` in `theorem ibTrajectory_step_descent_frozenTarget` — proof appears to close via minimal tactic one-liner
  - L59 [soft] `skeletal-proof` in `theorem ibBlahutArimotoStep_variational_descent_currentTarget` — proof appears to close via minimal tactic one-liner
  - L87 [soft] `skeletal-proof` in `theorem ibTrajectory_variational_descent_currentTarget` — proof appears to close via minimal tactic one-liner

