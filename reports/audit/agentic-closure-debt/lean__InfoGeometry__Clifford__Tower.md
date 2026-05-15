# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:20.264314+00:00`
Root: `lean/InfoGeometry/Clifford/Tower.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **4**
- Hard: **0**
- Soft: **3**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Clifford/Tower.lean` | `advisory` | 7 | 0 | 3 | 1 | 4 |

## Findings by file

### `lean/InfoGeometry/Clifford/Tower.lean`
- module: `InfoGeometry.Clifford.Tower`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L17 [soft] `simp-law-injection` in `simp-declaration Q11_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L50 [soft] `simp-law-injection` in `simp-declaration Qsplit_zero_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L54 [soft] `simp-law-injection` in `simp-declaration Qsplit_succ_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

