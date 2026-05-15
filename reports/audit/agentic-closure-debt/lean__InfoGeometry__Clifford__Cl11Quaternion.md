# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:16.753476+00:00`
Root: `lean/InfoGeometry/Clifford/Cl11Quaternion.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **2**
- Hard: **0**
- Soft: **1**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Clifford/Cl11Quaternion.lean` | `advisory` | 3 | 0 | 1 | 1 | 2 |

## Findings by file

### `lean/InfoGeometry/Clifford/Cl11Quaternion.lean`
- module: `InfoGeometry.Clifford.Cl11Quaternion`
- status: `advisory`
- debt_score: `3`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L38 [soft] `simp-law-injection` in `simp-declaration kM_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

