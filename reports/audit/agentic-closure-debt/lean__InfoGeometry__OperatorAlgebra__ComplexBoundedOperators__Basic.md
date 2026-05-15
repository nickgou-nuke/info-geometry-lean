# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:07.977140+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/Basic.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **21**
- Hard: **0**
- Soft: **20**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/Basic.lean` | `advisory` | 41 | 0 | 20 | 1 | 21 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/Basic.lean`
- module: `InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.Basic`
- status: `advisory`
- debt_score: `41`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L42 [soft] `simp-law-injection` in `simp-declaration apply_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L44 [soft] `skeletal-proof` in `theorem apply_eq` — proof appears to close via minimal tactic one-liner
  - L56 [soft] `simp-law-injection` in `simp-declaration id_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L58 [soft] `skeletal-proof` in `theorem id_apply` — proof appears to close via minimal tactic one-liner
  - L65 [soft] `simp-law-injection` in `simp-declaration comp_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L67 [soft] `skeletal-proof` in `theorem comp_apply` — proof appears to close via minimal tactic one-liner
  - L70 [soft] `simp-law-injection` in `simp-declaration comp_id` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L76 [soft] `simp-law-injection` in `simp-declaration id_comp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L87 [soft] `simp-law-injection` in `simp-declaration zero_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L91 [soft] `skeletal-proof` in `theorem zero_apply` — proof appears to close via minimal tactic one-liner
  - L94 [soft] `simp-law-injection` in `simp-declaration add_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L96 [soft] `skeletal-proof` in `theorem add_apply` — proof appears to close via minimal tactic one-liner
  - L99 [soft] `simp-law-injection` in `simp-declaration neg_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L101 [soft] `skeletal-proof` in `theorem neg_apply` — proof appears to close via minimal tactic one-liner
  - L104 [soft] `simp-law-injection` in `simp-declaration sub_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L106 [soft] `skeletal-proof` in `theorem sub_apply` — proof appears to close via minimal tactic one-liner
  - L109 [soft] `simp-law-injection` in `simp-declaration smul_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L111 [soft] `skeletal-proof` in `theorem smul_apply` — proof appears to close via minimal tactic one-liner
  - L139 [soft] `simp-law-injection` in `simp-declaration comp_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L145 [soft] `simp-law-injection` in `simp-declaration zero_comp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

