# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:08.399081+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/ComplexVectorSpaces.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **12**
- Hard: **0**
- Soft: **10**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/ComplexVectorSpaces.lean` | `advisory` | 22 | 0 | 10 | 2 | 12 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/ComplexVectorSpaces.lean`
- module: `InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.ComplexVectorSpaces`
- status: `advisory`
- debt_score: `22`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L31 [soft] `skeletal-proof` in `theorem complex_smul_re_im` — proof appears to close via minimal tactic one-liner
  - L48 [soft] `simp-law-injection` in `simp-declaration neg_one_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L50 [soft] `skeletal-proof` in `theorem neg_one_smul` — proof appears to close via minimal tactic one-liner
  - L53 [soft] `skeletal-proof` in `theorem two_smul` — proof appears to close via minimal tactic one-liner
  - L57 [soft] `simp-law-injection` in `simp-declaration half_smul_double` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L59 [soft] `skeletal-proof` in `theorem half_smul_double` — proof appears to close via minimal tactic one-liner
  - L68 [soft] `simp-law-injection` in `simp-declaration restrictScalarsReal_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L70 [soft] `skeletal-proof` in `theorem restrictScalarsReal_apply` — proof appears to close via minimal tactic one-liner
  - L73 [soft] `simp-law-injection` in `simp-declaration norm_restrictScalarsReal` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L78 [advisory] `existential-packaging` in `theorem mem_complex_span_singleton_iff` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L78 [soft] `skeletal-proof` in `theorem mem_complex_span_singleton_iff` — proof appears to close via minimal tactic one-liner

