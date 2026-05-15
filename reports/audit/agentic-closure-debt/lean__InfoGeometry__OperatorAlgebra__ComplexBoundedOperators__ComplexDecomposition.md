# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:08.259650+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/ComplexDecomposition.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **12**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/ComplexDecomposition.lean` | `advisory` | 25 | 0 | 12 | 1 | 13 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/ComplexDecomposition.lean`
- module: `InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.ComplexDecomposition`
- status: `advisory`
- debt_score: `25`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L48 [soft] `simp-law-injection` in `simp-declaration complexReContinuousMap_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L50 [soft] `skeletal-proof` in `theorem complexReContinuousMap_apply` — proof appears to close via minimal tactic one-liner
  - L52 [soft] `simp-law-injection` in `simp-declaration complexImContinuousMap_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L54 [soft] `skeletal-proof` in `theorem complexImContinuousMap_apply` — proof appears to close via minimal tactic one-liner
  - L56 [soft] `simp-law-injection` in `simp-declaration complexOfRealContinuousMap_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L58 [soft] `skeletal-proof` in `theorem complexOfRealContinuousMap_apply` — proof appears to close via minimal tactic one-liner
  - L60 [soft] `simp-law-injection` in `simp-declaration ccRe_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L65 [soft] `simp-law-injection` in `simp-declaration ccIm_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L70 [soft] `simp-law-injection` in `simp-declaration ccOfReal_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L75 [soft] `simp-law-injection` in `simp-declaration ccRe_ccOfReal` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L81 [soft] `simp-law-injection` in `simp-declaration ccIm_ccOfReal` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L87 [soft] `simp-law-injection` in `simp-declaration ccOfReal_re_add_I_smul_ccOfReal_im` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

