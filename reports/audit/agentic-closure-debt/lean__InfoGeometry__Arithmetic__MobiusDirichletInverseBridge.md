# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:32.270710+00:00`
Root: `lean/InfoGeometry/Arithmetic/MobiusDirichletInverseBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **4**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Arithmetic/MobiusDirichletInverseBridge.lean` | `advisory` | 9 | 0 | 4 | 1 | 5 |

## Findings by file

### `lean/InfoGeometry/Arithmetic/MobiusDirichletInverseBridge.lean`
- module: `InfoGeometry.Arithmetic.MobiusDirichletInverseBridge`
- status: `advisory`
- debt_score: `9`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L83 [soft] `simp-law-injection` in `simp-declaration finiteMobiusDirichletPolynomial_empty` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L86 [soft] `skeletal-proof` in `theorem finiteMobiusDirichletPolynomial_empty` — proof appears to close via minimal tactic one-liner
  - L91 [soft] `simp-law-injection` in `simp-declaration finiteFermionicEulerProduct_empty` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L94 [soft] `skeletal-proof` in `theorem finiteFermionicEulerProduct_empty` — proof appears to close via minimal tactic one-liner

