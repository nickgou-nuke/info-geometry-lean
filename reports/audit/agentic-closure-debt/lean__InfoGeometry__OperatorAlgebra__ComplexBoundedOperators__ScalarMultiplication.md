# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:10.605576+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/ScalarMultiplication.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **6**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/ScalarMultiplication.lean` | `advisory` | 13 | 0 | 6 | 1 | 7 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/ScalarMultiplication.lean`
- module: `InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.ScalarMultiplication`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L30 [soft] `simp-law-injection` in `simp-declaration scalarOp_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L32 [soft] `skeletal-proof` in `theorem scalarOp_apply` — proof appears to close via minimal tactic one-liner
  - L48 [soft] `simp-law-injection` in `simp-declaration leftMul_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L50 [soft] `skeletal-proof` in `theorem leftMul_apply` — proof appears to close via minimal tactic one-liner
  - L61 [soft] `simp-law-injection` in `simp-declaration rightMul_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L63 [soft] `skeletal-proof` in `theorem rightMul_apply` — proof appears to close via minimal tactic one-liner

