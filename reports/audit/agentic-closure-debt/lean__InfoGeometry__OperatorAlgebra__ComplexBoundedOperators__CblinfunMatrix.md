# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:08.128139+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/CblinfunMatrix.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **18**
- Hard: **0**
- Soft: **17**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/CblinfunMatrix.lean` | `advisory` | 35 | 0 | 17 | 1 | 18 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/CblinfunMatrix.lean`
- module: `InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix`
- status: `advisory`
- debt_score: `35`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L36 [soft] `simp-law-injection` in `simp-declaration matrixOfOp_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L38 [soft] `skeletal-proof` in `theorem matrixOfOp_apply` — proof appears to close via minimal tactic one-liner
  - L48 [soft] `simp-law-injection` in `simp-declaration matrixOfOp_matrixOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L56 [soft] `simp-law-injection` in `simp-declaration matrixOp_matrixOfOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L59 [soft] `skeletal-proof` in `theorem matrixOp_matrixOfOp` — proof appears to close via minimal tactic one-liner
  - L96 [soft] `simp-law-injection` in `simp-declaration matrixOfOp_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L102 [soft] `simp-law-injection` in `simp-declaration matrixOfOp_add` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L109 [soft] `simp-law-injection` in `simp-declaration matrixOfOp_neg` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L116 [soft] `simp-law-injection` in `simp-declaration matrixOfOp_sub` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L123 [soft] `simp-law-injection` in `simp-declaration matrixOfOp_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L130 [soft] `simp-law-injection` in `simp-declaration matrixOfOp_id` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L136 [soft] `simp-law-injection` in `simp-declaration matrixOfOp_comp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L144 [soft] `simp-law-injection` in `simp-declaration matrixOp_of_add` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L150 [soft] `simp-law-injection` in `simp-declaration matrixOp_of_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L156 [soft] `simp-law-injection` in `simp-declaration matrixOp_of_id` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L167 [soft] `skeletal-proof` in `theorem finiteKet_inner_eq_dotProduct` — proof appears to close via minimal tactic one-liner
  - L191 [soft] `simp-law-injection` in `simp-declaration matrixOfOp_adjoint` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

