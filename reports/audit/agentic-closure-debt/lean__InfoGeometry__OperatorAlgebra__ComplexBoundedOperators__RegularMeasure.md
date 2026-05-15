# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:10.239875+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/RegularMeasure.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **1**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/RegularMeasure.lean` | `advisory` | 7 | 0 | 1 | 5 | 6 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/RegularMeasure.lean`
- module: `InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.RegularMeasure`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L69 [soft] `skeletal-proof` in `theorem iInter_nbh_eq_closure` — proof appears to close via minimal tactic one-liner
  - L84 [advisory] `local-hypothesis-injection` in `theorem iInter_nbh_eq_closure` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L199 [advisory] `existential-packaging` in `theorem exists_isCompact_lt_add_of_innerRegularCompactLTTop` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L209 [advisory] `existential-packaging` in `theorem exists_isOpen_lt_add_of_outerRegular` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L289 [advisory] `existential-packaging` in `theorem isTightMeasureSet_iff_exists_isCompact_measure_compl_le` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

