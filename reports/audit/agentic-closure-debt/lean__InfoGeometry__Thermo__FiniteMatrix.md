# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:46.652870+00:00`
Root: `lean/InfoGeometry/Thermo/FiniteMatrix.lean`
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
| `lean/InfoGeometry/Thermo/FiniteMatrix.lean` | `advisory` | 5 | 0 | 2 | 1 | 3 |

## Findings by file

### `lean/InfoGeometry/Thermo/FiniteMatrix.lean`
- module: `InfoGeometry.Thermo.FiniteMatrix`
- status: `advisory`
- debt_score: `5`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L43 [soft] `skeletal-proof` in `lemma partitionFunction_ne_zero` — proof appears to close via minimal tactic one-liner
  - L79 [soft] `simp-law-injection` in `simp-declaration modularShift_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

