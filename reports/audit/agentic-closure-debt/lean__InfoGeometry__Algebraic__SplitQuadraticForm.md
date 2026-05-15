# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:29.814112+00:00`
Root: `lean/InfoGeometry/Algebraic/SplitQuadraticForm.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **17**
- Hard: **0**
- Soft: **15**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Algebraic/SplitQuadraticForm.lean` | `advisory` | 32 | 0 | 15 | 2 | 17 |

## Findings by file

### `lean/InfoGeometry/Algebraic/SplitQuadraticForm.lean`
- module: `InfoGeometry.Algebraic.SplitQuadraticForm`
- status: `advisory`
- debt_score: `32`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L44 [soft] `simp-law-injection` in `simp-declaration splitWeight_inl` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L46 [soft] `skeletal-proof` in `theorem splitWeight_inl` — proof appears to close via minimal tactic one-liner
  - L49 [soft] `simp-law-injection` in `simp-declaration splitWeight_inr` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L51 [soft] `skeletal-proof` in `theorem splitWeight_inr` — proof appears to close via minimal tactic one-liner
  - L63 [soft] `simp-law-injection` in `simp-declaration splitQuadraticForm_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L65 [soft] `skeletal-proof` in `theorem splitQuadraticForm_apply` — proof appears to close via minimal tactic one-liner
  - L74 [soft] `simp-law-injection` in `simp-declaration splitBasisVector_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L76 [soft] `skeletal-proof` in `theorem splitBasisVector_self` — proof appears to close via minimal tactic one-liner
  - L79 [soft] `simp-law-injection` in `simp-declaration splitBasisVector_ne` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L81 [soft] `skeletal-proof` in `theorem splitBasisVector_ne` — proof appears to close via minimal tactic one-liner
  - L84 [soft] `simp-law-injection` in `simp-declaration splitQuadraticForm_basisVector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L91 [soft] `simp-law-injection` in `simp-declaration splitQuadraticForm_posBasisVector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L93 [soft] `skeletal-proof` in `theorem splitQuadraticForm_posBasisVector` — proof appears to close via minimal tactic one-liner
  - L97 [soft] `simp-law-injection` in `simp-declaration splitQuadraticForm_negBasisVector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L99 [soft] `skeletal-proof` in `theorem splitQuadraticForm_negBasisVector` — proof appears to close via minimal tactic one-liner
  - L119 [advisory] `existential-packaging` in `theorem narainQuadratic_even` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

