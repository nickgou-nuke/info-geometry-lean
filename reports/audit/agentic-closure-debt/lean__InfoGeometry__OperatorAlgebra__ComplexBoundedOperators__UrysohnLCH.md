# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:10.747226+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/UrysohnLCH.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **0**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/UrysohnLCH.lean` | `advisory` | 5 | 0 | 0 | 5 | 5 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/UrysohnLCH.lean`
- module: `InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.UrysohnLCH`
- status: `advisory`
- debt_score: `5`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L21 [advisory] `existential-packaging` in `theorem exists_bump_one_on_compact_support_subset_open` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L43 [advisory] `existential-packaging` in `theorem exists_bump_one_on_compact_zero_off_open` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L64 [advisory] `existential-packaging` in `theorem exists_bump_zero_one_of_disjoint_compacts` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L91 [advisory] `existential-packaging` in `theorem exists_continuous_one_zero_of_compact_closed` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

