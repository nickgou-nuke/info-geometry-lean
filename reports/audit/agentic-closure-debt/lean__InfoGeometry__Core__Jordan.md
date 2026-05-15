# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:24.449453+00:00`
Root: `lean/InfoGeometry/Core/Jordan.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **6**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Core/Jordan.lean` | `advisory` | 13 | 0 | 6 | 1 | 7 |

## Findings by file

### `lean/InfoGeometry/Core/Jordan.lean`
- module: `InfoGeometry.Core.Jordan`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L20 [soft] `simp-law-injection` in `simp-declaration jordan_prod_comm` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L23 [soft] `simp-law-injection` in `simp-declaration jordan_prod_add_left` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L27 [soft] `simp-law-injection` in `simp-declaration jordan_prod_add_right` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L31 [soft] `simp-law-injection` in `simp-declaration jordan_prod_smul_left` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L35 [soft] `simp-law-injection` in `simp-declaration jordan_prod_smul_right` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L51 [soft] `simp-law-injection` in `simp-declaration spd_transpose_eq_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

