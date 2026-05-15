# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:55.652011+00:00`
Root: `lean/InfoGeometry/LLM/CompilerRosetta.lean`
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
| `lean/InfoGeometry/LLM/CompilerRosetta.lean` | `advisory` | 9 | 0 | 4 | 1 | 5 |

## Findings by file

### `lean/InfoGeometry/LLM/CompilerRosetta.lean`
- module: `InfoGeometry.LLM.CompilerRosetta`
- status: `advisory`
- debt_score: `9`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L61 [soft] `simp-law-injection` in `simp-declaration sourceMetavariableDebt_ofTacticInfo` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L66 [soft] `simp-law-injection` in `simp-declaration targetMetavariableDebt_ofTacticInfo` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L71 [soft] `simp-law-injection` in `simp-declaration transportCost_nonneg` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L76 [soft] `skeletal-proof` in `theorem acceptanceFromTacticInfo_uphill_lt_cooling` — proof appears to close via minimal tactic one-liner

