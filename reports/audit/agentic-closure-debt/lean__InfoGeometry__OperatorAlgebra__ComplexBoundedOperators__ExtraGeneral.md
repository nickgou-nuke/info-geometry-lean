# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:08.510225+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/ExtraGeneral.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **4**
- Hard: **0**
- Soft: **2**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/ExtraGeneral.lean` | `advisory` | 6 | 0 | 2 | 2 | 4 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/ExtraGeneral.lean`
- module: `InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.ExtraGeneral`
- status: `advisory`
- debt_score: `6`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L19 [advisory] `existential-packaging` in `theorem uniqueChoice` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L19 [soft] `classical-witness-smuggling` in `theorem uniqueChoice` — declaration uses Classical/choice/Nonempty witness extraction; require constructive payload readback or explicit nonconstructive boundary
  - L77 [soft] `skeletal-proof` in `theorem complex_star_mul_self_eq_normSq` — proof appears to close via minimal tactic one-liner

