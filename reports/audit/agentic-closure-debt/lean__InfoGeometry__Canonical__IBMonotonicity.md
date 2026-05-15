# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:18.380416+00:00`
Root: `lean/InfoGeometry/Canonical/IBMonotonicity.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **2**
- Hard: **0**
- Soft: **0**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/IBMonotonicity.lean` | `advisory` | 2 | 0 | 0 | 2 | 2 |

## Findings by file

### `lean/InfoGeometry/Canonical/IBMonotonicity.lean`
- module: `InfoGeometry.Canonical.IBMonotonicity`
- status: `advisory`
- debt_score: `2`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [advisory] `bridge-shaped-declaration` in `theorem IB_monotone_descent_of_witness` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

