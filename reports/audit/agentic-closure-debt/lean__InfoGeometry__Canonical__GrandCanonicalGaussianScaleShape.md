# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:11.806305+00:00`
Root: `lean/InfoGeometry/Canonical/GrandCanonicalGaussianScaleShape.lean`
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
| `lean/InfoGeometry/Canonical/GrandCanonicalGaussianScaleShape.lean` | `advisory` | 6 | 0 | 2 | 2 | 4 |

## Findings by file

### `lean/InfoGeometry/Canonical/GrandCanonicalGaussianScaleShape.lean`
- module: `InfoGeometry.Canonical.GrandCanonicalGaussianScaleShape`
- status: `advisory`
- debt_score: `6`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L109 [soft] `skeletal-proof` in `theorem generalizedKL_eq_ISShape_add_scaleTerm` — proof appears to close via minimal tactic one-liner
  - L146 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L164 [soft] `skeletal-proof` in `theorem kahlerPotentialRN_eq_scalarModularPotential_relativeVolumeChangeRN` — proof appears to close via minimal tactic one-liner

