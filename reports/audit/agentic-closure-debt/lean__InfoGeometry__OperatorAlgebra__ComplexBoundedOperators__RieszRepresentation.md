# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:10.484856+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/RieszRepresentation.lean`
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
| `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/RieszRepresentation.lean` | `advisory` | 19 | 0 | 9 | 1 | 10 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/RieszRepresentation.lean`
- module: `InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.RieszRepresentation`
- status: `advisory`
- debt_score: `19`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L44 [soft] `simp-law-injection` in `simp-declaration integral_realRieszMeasure` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L50 [soft] `skeletal-proof` in `theorem integral_realRieszMeasure` — proof appears to close via minimal tactic one-liner
  - L61 [soft] `simp-law-injection` in `simp-declaration realRieszMeasure_integralPositiveLinearMap` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L68 [soft] `skeletal-proof` in `theorem realRieszMeasure_integralPositiveLinearMap` — proof appears to close via minimal tactic one-liner
  - L73 [soft] `simp-law-injection` in `simp-declaration integralPositiveLinearMap_realRieszMeasure` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L80 [soft] `skeletal-proof` in `theorem integralPositiveLinearMap_realRieszMeasure` — proof appears to close via minimal tactic one-liner
  - L118 [soft] `simp-law-injection` in `simp-declaration complexIntegralLinearMap_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L119 [soft] `skeletal-proof` in `theorem complexIntegralLinearMap_apply` — proof appears to close via minimal tactic one-liner
  - L125 [soft] `simp-law-injection` in `simp-declaration complexIntegralLinearMap_ccOfReal` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

