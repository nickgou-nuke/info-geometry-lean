# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:08.908890+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/ExtraOrderedFields.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **21**
- Hard: **0**
- Soft: **18**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/ExtraOrderedFields.lean` | `advisory` | 39 | 0 | 18 | 3 | 21 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/ExtraOrderedFields.lean`
- module: `InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.ExtraOrderedFields`
- status: `advisory`
- debt_score: `39`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L33 [soft] `simp-law-injection` in `simp-declaration zero_eq_one_divide_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L39 [soft] `simp-law-injection` in `simp-declaration one_divide_eq_zero_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L41 [soft] `skeletal-proof` in `theorem one_divide_eq_zero_iff` — proof appears to close via minimal tactic one-liner
  - L44 [soft] `simp-law-injection` in `simp-declaration eq_divide_eq_one_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L46 [soft] `skeletal-proof` in `theorem eq_divide_eq_one_iff` — proof appears to close via minimal tactic one-liner
  - L58 [soft] `simp-law-injection` in `simp-declaration divide_eq_eq_one_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L60 [soft] `skeletal-proof` in `theorem divide_eq_eq_one_iff` — proof appears to close via minimal tactic one-liner
  - L87 [soft] `skeletal-proof` in `theorem nonzero_abs_inverse` — proof appears to close via minimal tactic one-liner
  - L91 [soft] `skeletal-proof` in `theorem nonzero_abs_divide` — proof appears to close via minimal tactic one-liner
  - L100 [soft] `simp-law-injection` in `simp-declaration inverse_positive_iff_positive` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L105 [soft] `simp-law-injection` in `simp-declaration inverse_nonnegative_iff_nonnegative` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L115 [advisory] `local-hypothesis-injection` in `theorem one_less_inverse_iff` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L124 [advisory] `local-hypothesis-injection` in `theorem one_le_inverse_iff` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L132 [soft] `skeletal-proof` in `theorem complex_ofReal_re_mono` — proof appears to close via minimal tactic one-liner
  - L136 [soft] `simp-law-injection` in `simp-declaration complex_ofReal_re_le_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L138 [soft] `skeletal-proof` in `theorem complex_ofReal_re_le_iff` — proof appears to close via minimal tactic one-liner
  - L141 [soft] `simp-law-injection` in `simp-declaration complex_ofReal_re_lt_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L143 [soft] `skeletal-proof` in `theorem complex_ofReal_re_lt_iff` — proof appears to close via minimal tactic one-liner
  - L146 [soft] `simp-law-injection` in `simp-declaration complex_ofReal_im` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L148 [soft] `skeletal-proof` in `theorem complex_ofReal_im` — proof appears to close via minimal tactic one-liner

