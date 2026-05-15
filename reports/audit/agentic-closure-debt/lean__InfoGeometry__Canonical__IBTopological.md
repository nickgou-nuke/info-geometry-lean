# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:19.110497+00:00`
Root: `lean/InfoGeometry/Canonical/IBTopological.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **3**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/IBTopological.lean` | `advisory` | 11 | 0 | 3 | 5 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/IBTopological.lean`
- module: `InfoGeometry.Canonical.IBTopological`
- status: `advisory`
- debt_score: `11`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L14 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L14 [soft] `section-law-variable` in `variable D` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L15 [advisory] `existential-packaging` in `def F` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L21 [advisory] `existential-packaging` in `def Gibbs` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L26 [advisory] `existential-packaging` in `theorem F_deriv_eq_neg_gibbsExpectation` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L26 [soft] `skeletal-proof` in `theorem F_deriv_eq_neg_gibbsExpectation` — proof appears to close via minimal tactic one-liner
  - L41 [soft] `skeletal-proof` in `theorem F_secondDeriv_eq_variance` — proof appears to close via minimal tactic one-liner

