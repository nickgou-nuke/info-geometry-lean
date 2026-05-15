# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:18.980874+00:00`
Root: `lean/InfoGeometry/Canonical/IBTilted.lean`
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
| `lean/InfoGeometry/Canonical/IBTilted.lean` | `advisory` | 5 | 0 | 2 | 1 | 3 |

## Findings by file

### `lean/InfoGeometry/Canonical/IBTilted.lean`
- module: `InfoGeometry.Canonical.IBTilted`
- status: `advisory`
- debt_score: `5`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L50 [soft] `simp-law-injection` in `simp-declaration frozenWeight_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L62 [soft] `simp-law-injection` in `simp-declaration baScoreFrozen_eq_prior_mul_frozenWeight` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

