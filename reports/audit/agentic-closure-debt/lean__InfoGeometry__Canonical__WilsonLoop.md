# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:13.792334+00:00`
Root: `lean/InfoGeometry/Canonical/WilsonLoop.lean`
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
| `lean/InfoGeometry/Canonical/WilsonLoop.lean` | `advisory` | 7 | 0 | 3 | 1 | 4 |

## Findings by file

### `lean/InfoGeometry/Canonical/WilsonLoop.lean`
- module: `InfoGeometry.Canonical.WilsonLoop`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L56 [soft] `simp-law-injection` in `simp-declaration wilsonLoopDiscrete_eq_norm` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L62 [soft] `simp-law-injection` in `simp-declaration chiralPathWeight_eq_holonomy_mul_gibbs` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L70 [soft] `simp-law-injection` in `simp-declaration expectedHolonomy_eq_partition_ratio` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

