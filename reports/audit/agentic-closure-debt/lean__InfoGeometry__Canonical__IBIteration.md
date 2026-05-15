# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:18.147496+00:00`
Root: `lean/InfoGeometry/Canonical/IBIteration.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **4**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/IBIteration.lean` | `advisory` | 14 | 0 | 4 | 6 | 10 |

## Findings by file

### `lean/InfoGeometry/Canonical/IBIteration.lean`
- module: `InfoGeometry.Canonical.IBIteration`
- status: `advisory`
- debt_score: `14`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L19 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L21 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L22 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L23 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L23 [soft] `section-law-variable` in `variable hInt` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L29 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L29 [soft] `section-law-variable` in `variable h_meas` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L61 [soft] `skeletal-proof` in `lemma IBStep_apply` — proof appears to close via minimal tactic one-liner
  - L71 [soft] `skeletal-proof` in `lemma IBStepMeasure_eq_comp` — proof appears to close via minimal tactic one-liner

