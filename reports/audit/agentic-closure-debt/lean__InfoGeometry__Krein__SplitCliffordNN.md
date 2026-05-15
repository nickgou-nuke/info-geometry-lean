# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:54.390496+00:00`
Root: `lean/InfoGeometry/Krein/SplitCliffordNN.lean`
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
| `lean/InfoGeometry/Krein/SplitCliffordNN.lean` | `advisory` | 9 | 0 | 4 | 1 | 5 |

## Findings by file

### `lean/InfoGeometry/Krein/SplitCliffordNN.lean`
- module: `InfoGeometry.Krein.SplitCliffordNN`
- status: `advisory`
- debt_score: `9`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L44 [soft] `simp-law-injection` in `simp-declaration gamma_head_null_car` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L51 [soft] `simp-law-injection` in `simp-declaration quad_rankOne_symm` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L57 [soft] `simp-law-injection` in `simp-declaration quad_rankOne_headNullMinus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L62 [soft] `simp-law-injection` in `simp-declaration quad_rankOne_headNullPlus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

