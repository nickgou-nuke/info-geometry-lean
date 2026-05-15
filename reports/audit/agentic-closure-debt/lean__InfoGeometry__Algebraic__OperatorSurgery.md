# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:29.058391+00:00`
Root: `lean/InfoGeometry/Algebraic/OperatorSurgery.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **4**
- Hard: **0**
- Soft: **3**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Algebraic/OperatorSurgery.lean` | `advisory` | 7 | 0 | 3 | 1 | 4 |

## Findings by file

### `lean/InfoGeometry/Algebraic/OperatorSurgery.lean`
- module: `InfoGeometry.Algebraic.OperatorSurgery`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L44 [soft] `skeletal-proof` in `theorem null_idempotent` — proof appears to close via minimal tactic one-liner
  - L48 [soft] `skeletal-proof` in `theorem core_null_orthogonal` — proof appears to close via minimal tactic one-liner
  - L52 [soft] `skeletal-proof` in `theorem partition_of_unity` — proof appears to close via minimal tactic one-liner

