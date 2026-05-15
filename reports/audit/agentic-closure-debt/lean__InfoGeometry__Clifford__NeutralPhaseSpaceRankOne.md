# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:18.653886+00:00`
Root: `lean/InfoGeometry/Clifford/NeutralPhaseSpaceRankOne.lean`
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
| `lean/InfoGeometry/Clifford/NeutralPhaseSpaceRankOne.lean` | `advisory` | 7 | 0 | 3 | 1 | 4 |

## Findings by file

### `lean/InfoGeometry/Clifford/NeutralPhaseSpaceRankOne.lean`
- module: `InfoGeometry.Clifford.NeutralPhaseSpaceRankOne`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L57 [soft] `simp-law-injection` in `simp-declaration dualRealProjection_section` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L62 [soft] `simp-law-injection` in `simp-declaration dualRealSection_projection` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L163 [soft] `simp-law-injection` in `simp-declaration rankOneIsometry_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

