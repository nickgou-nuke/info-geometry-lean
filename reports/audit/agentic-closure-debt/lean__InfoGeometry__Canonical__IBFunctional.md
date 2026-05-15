# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:17.891131+00:00`
Root: `lean/InfoGeometry/Canonical/IBFunctional.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **1**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/IBFunctional.lean` | `advisory` | 11 | 0 | 1 | 9 | 10 |

## Findings by file

### `lean/InfoGeometry/Canonical/IBFunctional.lean`
- module: `InfoGeometry.Canonical.IBFunctional`
- status: `advisory`
- debt_score: `11`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L13 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L15 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L16 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L33 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L35 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L35 [soft] `section-law-variable` in `variable encoder` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L36 [advisory] `existential-packaging` in `def bindEncoderMeasure` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L48 [advisory] `existential-packaging` in `def IBMarginalize` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L57 [advisory] `existential-packaging` in `lemma IBMarginalize_apply` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

