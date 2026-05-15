# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:09.714988+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/L2Multiplier.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **8**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/L2Multiplier.lean` | `advisory` | 17 | 0 | 8 | 1 | 9 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/L2Multiplier.lean`
- module: `InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.L2Multiplier`
- status: `advisory`
- debt_score: `17`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L60 [soft] `simp-law-injection` in `simp-declaration mulOp_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L62 [soft] `skeletal-proof` in `theorem mulOp_apply` — proof appears to close via minimal tactic one-liner
  - L65 [soft] `skeletal-proof` in `theorem mulOp_apply_ae` — proof appears to close via minimal tactic one-liner
  - L71 [soft] `skeletal-proof` in `theorem norm_mulOp_apply_le` — proof appears to close via minimal tactic one-liner
  - L126 [soft] `simp-law-injection` in `simp-declaration discreteMulOp_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L128 [soft] `skeletal-proof` in `theorem discreteMulOp_apply` — proof appears to close via minimal tactic one-liner
  - L143 [soft] `skeletal-proof` in `theorem norm_discreteMulOp_apply_le` — proof appears to close via minimal tactic one-liner
  - L150 [soft] `skeletal-proof` in `theorem norm_discreteMulOp_le` — proof appears to close via minimal tactic one-liner

