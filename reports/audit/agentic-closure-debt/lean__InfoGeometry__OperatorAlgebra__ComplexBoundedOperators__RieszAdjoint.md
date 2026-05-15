# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:10.354664+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/RieszAdjoint.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **15**
- Hard: **0**
- Soft: **14**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/RieszAdjoint.lean` | `advisory` | 29 | 0 | 14 | 1 | 15 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/RieszAdjoint.lean`
- module: `InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.RieszAdjoint`
- status: `advisory`
- debt_score: `29`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L29 [soft] `simp-law-injection` in `simp-declaration rieszMap_apply_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L41 [soft] `simp-law-injection` in `simp-declaration rieszEquiv_apply_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L54 [soft] `simp-law-injection` in `simp-declaration cadjoint_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L56 [soft] `skeletal-proof` in `theorem cadjoint_apply` — proof appears to close via minimal tactic one-liner
  - L64 [soft] `skeletal-proof` in `theorem cadjoint_inner_left` — proof appears to close via minimal tactic one-liner
  - L68 [soft] `simp-law-injection` in `simp-declaration cadjoint_id` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L77 [soft] `simp-law-injection` in `simp-declaration cadjoint_cadjoint` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L79 [soft] `skeletal-proof` in `theorem cadjoint_cadjoint` — proof appears to close via minimal tactic one-liner
  - L82 [soft] `simp-law-injection` in `simp-declaration norm_cadjoint` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L84 [soft] `skeletal-proof` in `theorem norm_cadjoint` — proof appears to close via minimal tactic one-liner
  - L87 [soft] `skeletal-proof` in `theorem cadjoint_eq_iff` — proof appears to close via minimal tactic one-liner
  - L91 [soft] `skeletal-proof` in `theorem star_eq_cadjoint` — proof appears to close via minimal tactic one-liner
  - L95 [soft] `skeletal-proof` in `theorem isSelfAdjoint_iff_cadjoint_eq` — proof appears to close via minimal tactic one-liner
  - L99 [soft] `skeletal-proof` in `theorem isSelfAdjoint.cadjoint_eq` — proof appears to close via minimal tactic one-liner

