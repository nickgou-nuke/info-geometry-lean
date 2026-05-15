# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:51.459974+00:00`
Root: `lean/InfoGeometry/Canonical/ChiralGravity.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **4**
- Hard: **0**
- Soft: **2**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ChiralGravity.lean` | `advisory` | 6 | 0 | 2 | 2 | 4 |

## Findings by file

### `lean/InfoGeometry/Canonical/ChiralGravity.lean`
- module: `InfoGeometry.Canonical.ChiralGravity`
- status: `advisory`
- debt_score: `6`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L22 [soft] `simp-law-injection` in `simp-declaration anomalyEinsteinResidualAt_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L44 [soft] `skeletal-proof` in `lemma anomalyEinsteinResidual_eq_kappa_mul_metric` — proof appears to close via minimal tactic one-liner
  - L102 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

