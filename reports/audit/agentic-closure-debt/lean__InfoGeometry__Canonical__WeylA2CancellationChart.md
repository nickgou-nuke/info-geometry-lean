# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:10.437333+00:00`
Root: `lean/InfoGeometry/Canonical/WeylA2CancellationChart.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **1**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/WeylA2CancellationChart.lean` | `advisory` | 8 | 0 | 1 | 6 | 7 |

## Findings by file

### `lean/InfoGeometry/Canonical/WeylA2CancellationChart.lean`
- module: `InfoGeometry.Canonical.WeylA2CancellationChart`
- status: `advisory`
- debt_score: `8`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L33 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L75 [advisory] `existential-packaging` in `theorem denominator_eq_zero_iff_collision` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L82 [advisory] `existential-packaging` in `theorem numerator_eq_zero_iff_expCollision` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L106 [soft] `skeletal-proof` in `theorem quotient_eq_ratio` — proof appears to close via minimal tactic one-liner
  - L111 [advisory] `bridge-shaped-declaration` in `theorem concrete_a2_cancellation_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L111 [advisory] `existential-packaging` in `theorem concrete_a2_cancellation_packet` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

