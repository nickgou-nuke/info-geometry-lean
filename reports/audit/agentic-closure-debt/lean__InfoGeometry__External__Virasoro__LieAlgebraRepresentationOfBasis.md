# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:32.284586+00:00`
Root: `lean/InfoGeometry/External/Virasoro/LieAlgebraRepresentationOfBasis.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **3**
- Hard: **0**
- Soft: **2**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/External/Virasoro/LieAlgebraRepresentationOfBasis.lean` | `advisory` | 5 | 0 | 2 | 1 | 3 |

## Findings by file

### `lean/InfoGeometry/External/Virasoro/LieAlgebraRepresentationOfBasis.lean`
- module: `InfoGeometry.External.Virasoro.LieAlgebraRepresentationOfBasis`
- status: `advisory`
- debt_score: `5`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L38 [soft] `skeletal-proof` in `lemma Representation.apply_bracket_eq_commutator` — proof appears to close via minimal tactic one-liner
  - L58 [soft] `simp-law-injection` in `simp-declaration representationOfBasisAux_apply_basis` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

