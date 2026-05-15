# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:50.729328+00:00`
Root: `lean/InfoGeometry/Krein/DoubledSpaceMatrix.lean`
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
| `lean/InfoGeometry/Krein/DoubledSpaceMatrix.lean` | `advisory` | 5 | 0 | 2 | 1 | 3 |

## Findings by file

### `lean/InfoGeometry/Krein/DoubledSpaceMatrix.lean`
- module: `InfoGeometry.Krein.DoubledSpaceMatrix`
- status: `advisory`
- debt_score: `5`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L28 [soft] `simp-law-injection` in `simp-declaration ofDoubledColumn_toDoubledColumn` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L34 [soft] `simp-law-injection` in `simp-declaration toDoubledColumn_ofDoubledColumn` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

