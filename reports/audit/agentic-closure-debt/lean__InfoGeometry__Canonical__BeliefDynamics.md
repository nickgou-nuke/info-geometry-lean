# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:42.105827+00:00`
Root: `lean/InfoGeometry/Canonical/BeliefDynamics.lean`
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
| `lean/InfoGeometry/Canonical/BeliefDynamics.lean` | `advisory` | 7 | 0 | 3 | 1 | 4 |

## Findings by file

### `lean/InfoGeometry/Canonical/BeliefDynamics.lean`
- module: `InfoGeometry.Canonical.BeliefDynamics`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L60 [soft] `simp-law-injection` in `simp-declaration parallelTransportE_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L64 [soft] `simp-law-injection` in `simp-declaration parallelTransportM_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L68 [soft] `simp-law-injection` in `simp-declaration quantumGeometryOp_eq_metricOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

