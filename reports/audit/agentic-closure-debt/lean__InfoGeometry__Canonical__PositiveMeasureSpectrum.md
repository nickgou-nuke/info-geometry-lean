# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:43.073801+00:00`
Root: `lean/InfoGeometry/Canonical/PositiveMeasureSpectrum.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **4**
- Hard: **0**
- Soft: **1**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/PositiveMeasureSpectrum.lean` | `advisory` | 5 | 0 | 1 | 3 | 4 |

## Findings by file

### `lean/InfoGeometry/Canonical/PositiveMeasureSpectrum.lean`
- module: `InfoGeometry.Canonical.PositiveMeasureSpectrum`
- status: `advisory`
- debt_score: `5`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L13 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L13 [soft] `section-law-variable` in `variable c` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L14 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface

