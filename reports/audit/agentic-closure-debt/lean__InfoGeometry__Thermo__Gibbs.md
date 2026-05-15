# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:47.022473+00:00`
Root: `lean/InfoGeometry/Thermo/Gibbs.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **3**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Thermo/Gibbs.lean` | `advisory` | 10 | 0 | 3 | 4 | 7 |

## Findings by file

### `lean/InfoGeometry/Thermo/Gibbs.lean`
- module: `InfoGeometry.Thermo.Gibbs`
- status: `advisory`
- debt_score: `10`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L43 [advisory] `existential-packaging` in `def freeEnergy` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L49 [soft] `simp-law-injection` in `simp-declaration freeEnergy_def'` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L84 [advisory] `existential-packaging` in `lemma Z_ne_zero` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L89 [advisory] `existential-packaging` in `lemma weight_pos` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L95 [soft] `skeletal-proof` in `lemma softMin_def` — proof appears to close via minimal tactic one-liner
  - L108 [soft] `skeletal-proof` in `lemma gibbsProb_sum_one` — proof appears to close via minimal tactic one-liner

