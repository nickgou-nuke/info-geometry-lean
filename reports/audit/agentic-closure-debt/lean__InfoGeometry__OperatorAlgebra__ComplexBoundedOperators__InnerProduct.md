# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:09.462931+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/InnerProduct.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **7**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/InnerProduct.lean` | `advisory` | 15 | 0 | 7 | 1 | 8 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/InnerProduct.lean`
- module: `InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.InnerProduct`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L23 [soft] `skeletal-proof` in `theorem cinner_commute` — proof appears to close via minimal tactic one-liner
  - L45 [soft] `skeletal-proof` in `theorem cinner_diff_left` — proof appears to close via minimal tactic one-liner
  - L49 [soft] `skeletal-proof` in `theorem cinner_diff_right` — proof appears to close via minimal tactic one-liner
  - L59 [soft] `simp-law-injection` in `simp-declaration im_cinner_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L64 [soft] `skeletal-proof` in `theorem cinner_smul_real_left` — proof appears to close via minimal tactic one-liner
  - L68 [soft] `skeletal-proof` in `theorem cinner_smul_real_right` — proof appears to close via minimal tactic one-liner
  - L138 [soft] `skeletal-proof` in `theorem sum_cinner` — proof appears to close via minimal tactic one-liner

