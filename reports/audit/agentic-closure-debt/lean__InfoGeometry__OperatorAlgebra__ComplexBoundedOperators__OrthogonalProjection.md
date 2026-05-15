# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:10.112140+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/OrthogonalProjection.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **14**
- Hard: **0**
- Soft: **13**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/OrthogonalProjection.lean` | `advisory` | 27 | 0 | 13 | 1 | 14 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/OrthogonalProjection.lean`
- module: `InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.OrthogonalProjection`
- status: `advisory`
- debt_score: `27`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L44 [soft] `simp-law-injection` in `simp-declaration top_orthogonalComplement_eq_bot` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L49 [soft] `simp-law-injection` in `simp-declaration bot_orthogonalComplement_eq_top` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L78 [soft] `simp-law-injection` in `simp-declaration projection_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L80 [soft] `skeletal-proof` in `theorem projection_apply` — proof appears to close via minimal tactic one-liner
  - L83 [soft] `simp-law-injection` in `simp-declaration projectionToSubmodule_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L85 [soft] `skeletal-proof` in `theorem projectionToSubmodule_apply` — proof appears to close via minimal tactic one-liner
  - L88 [soft] `skeletal-proof` in `theorem projection_mem` — proof appears to close via minimal tactic one-liner
  - L92 [soft] `skeletal-proof` in `theorem projection_eq_self_iff` — proof appears to close via minimal tactic one-liner
  - L96 [soft] `skeletal-proof` in `theorem projection_minimal` — proof appears to close via minimal tactic one-liner
  - L101 [soft] `skeletal-proof` in `theorem projection_range` — proof appears to close via minimal tactic one-liner
  - L105 [soft] `skeletal-proof` in `theorem projection_ker` — proof appears to close via minimal tactic one-liner
  - L109 [soft] `skeletal-proof` in `theorem projection_idempotent` — proof appears to close via minimal tactic one-liner
  - L113 [soft] `skeletal-proof` in `theorem projection_norm_le` — proof appears to close via minimal tactic one-liner

