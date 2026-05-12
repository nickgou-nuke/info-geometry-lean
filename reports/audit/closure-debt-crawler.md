# Lean Closure Debt Crawler Report

Generated: `2026-05-11T19:52:13.474054+00:00`
Root: `lean/InfoGeometry/Singular/MoorePenrose.lean`

## Summary

- Files scanned: **1**
- Findings: **2**
- Hard: **0**
- Soft: **1**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Singular/MoorePenrose.lean` | `advisory` | 3 | 0 | 1 | 1 | 2 |

## Findings by file

### `lean/InfoGeometry/Singular/MoorePenrose.lean`
- module: `InfoGeometry.Singular.MoorePenrose`
- status: `advisory`
- debt_score: `3`
- findings:
  - L82 [soft] `skeletal-proof` in `theorem MoorePenrose_unique` — proof appears to close via minimal tactic one-liner
  - L310 [advisory] `existential-packaging` in `theorem exists_moorePenroseInverse_of_closedRange` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

