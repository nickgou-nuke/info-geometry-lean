# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:14.231787+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/FiniteJonesOptics.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **7**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/FiniteJonesOptics.lean` | `advisory` | 15 | 0 | 7 | 1 | 8 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/FiniteJonesOptics.lean`
- module: `InfoGeometry.OperatorAlgebra.FiniteJonesOptics`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L74 [soft] `simp-law-injection` in `simp-declaration basis` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L76 [soft] `skeletal-proof` in `theorem basis` — proof appears to close via minimal tactic one-liner
  - L83 [soft] `simp-law-injection` in `simp-declaration coeff0` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L85 [soft] `skeletal-proof` in `theorem coeff0` — proof appears to close via minimal tactic one-liner
  - L92 [soft] `simp-law-injection` in `simp-declaration coeff1` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L94 [soft] `skeletal-proof` in `theorem coeff1` — proof appears to close via minimal tactic one-liner
  - L114 [soft] `skeletal-proof` in `theorem det2_diagJones` — proof appears to close via minimal tactic one-liner

