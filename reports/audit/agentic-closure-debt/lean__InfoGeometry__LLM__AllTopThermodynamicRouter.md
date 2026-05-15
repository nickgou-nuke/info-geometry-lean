# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:55.253664+00:00`
Root: `lean/InfoGeometry/LLM/AllTopThermodynamicRouter.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **5**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/LLM/AllTopThermodynamicRouter.lean` | `advisory` | 13 | 0 | 5 | 3 | 8 |

## Findings by file

### `lean/InfoGeometry/LLM/AllTopThermodynamicRouter.lean`
- module: `InfoGeometry.LLM.AllTopThermodynamicRouter`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L20 [advisory] `existential-packaging` in `def allTopWeight` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L32 [soft] `simp-law-injection` in `simp-declaration allTopWeight_eq_normalizedWeight` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L34 [soft] `skeletal-proof` in `theorem allTopWeight_eq_normalizedWeight` — proof appears to close via minimal tactic one-liner
  - L47 [soft] `skeletal-proof` in `theorem allTopWeight_sum_one` — proof appears to close via minimal tactic one-liner
  - L72 [advisory] `existential-packaging` in `def allTopMixture` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L81 [soft] `simp-law-injection` in `simp-declaration allTopMixture_eq_normalizedMixture` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L84 [soft] `skeletal-proof` in `theorem allTopMixture_eq_normalizedMixture` — proof appears to close via minimal tactic one-liner

