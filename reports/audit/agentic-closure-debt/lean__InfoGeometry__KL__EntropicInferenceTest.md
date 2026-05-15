# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:47.829874+00:00`
Root: `lean/InfoGeometry/KL/EntropicInferenceTest.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **4**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/KL/EntropicInferenceTest.lean` | `advisory` | 15 | 0 | 4 | 7 | 11 |

## Findings by file

### `lean/InfoGeometry/KL/EntropicInferenceTest.lean`
- module: `InfoGeometry.KL.EntropicInferenceTest`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L13 [advisory] `existential-packaging` in `abbrev X_test` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L126 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L128 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L129 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L129 [soft] `section-law-variable` in `variable hposp` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L130 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L130 [soft] `section-law-variable` in `variable hposq` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L131 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L131 [soft] `section-law-variable` in `variable hmarg` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L132 [soft] `skeletal-proof` in `lemma hq_support_of_strict_pos` — proof appears to close via minimal tactic one-liner

