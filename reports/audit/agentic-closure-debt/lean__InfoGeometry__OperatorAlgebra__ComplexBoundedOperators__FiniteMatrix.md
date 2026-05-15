# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:09.039721+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/FiniteMatrix.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **9**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/FiniteMatrix.lean` | `advisory` | 19 | 0 | 9 | 1 | 10 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/FiniteMatrix.lean`
- module: `InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.FiniteMatrix`
- status: `advisory`
- debt_score: `19`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L36 [soft] `simp-law-injection` in `simp-declaration ketPi_apply_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L38 [soft] `skeletal-proof` in `theorem ketPi_apply_self` — proof appears to close via minimal tactic one-liner
  - L41 [soft] `skeletal-proof` in `theorem ketPi_apply_of_ne` — proof appears to close via minimal tactic one-liner
  - L58 [soft] `simp-law-injection` in `simp-declaration matrixOp_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L60 [soft] `skeletal-proof` in `theorem matrixOp_apply` — proof appears to close via minimal tactic one-liner
  - L64 [soft] `skeletal-proof` in `theorem matrixOp_apply_ket` — proof appears to close via minimal tactic one-liner
  - L98 [soft] `simp-law-injection` in `simp-declaration conjTranspose_apply_entry` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L102 [soft] `skeletal-proof` in `theorem conjTranspose_apply_entry` — proof appears to close via minimal tactic one-liner
  - L105 [soft] `skeletal-proof` in `theorem matrixOp_conjTranspose_apply_ket` — proof appears to close via minimal tactic one-liner

