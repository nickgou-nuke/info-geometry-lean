# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:00.563367+00:00`
Root: `lean/InfoGeometry/Canonical/DiracSouriauOperator.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **3**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DiracSouriauOperator.lean` | `advisory` | 11 | 0 | 3 | 5 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/DiracSouriauOperator.lean`
- module: `InfoGeometry.Canonical.DiracSouriauOperator`
- status: `advisory`
- debt_score: `11`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L74 [soft] `skeletal-proof` in `theorem toMatrix_eq_fromBlocks` — proof appears to close via minimal tactic one-liner
  - L77 [advisory] `existential-packaging` in `theorem exists_drazinInverse` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L109 [advisory] `existential-packaging` in `def HasDrazinInverse` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L117 [advisory] `existential-packaging` in `theorem hasDrazinInverse_of_field` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L135 [soft] `classical-witness-smuggling` in `def DrazinWitnessContext.ofField` — declaration uses Classical/choice/Nonempty witness extraction; require constructive payload readback or explicit nonconstructive boundary
  - L162 [advisory] `existential-packaging` in `theorem exists_drazinInverse_of_hasDrazinInverse` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L202 [soft] `skeletal-proof` in `theorem supercharge_conservation_satisfied` — proof appears to close via minimal tactic one-liner

