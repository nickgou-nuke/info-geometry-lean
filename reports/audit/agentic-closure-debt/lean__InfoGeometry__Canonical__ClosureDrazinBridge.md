# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:54.511584+00:00`
Root: `lean/InfoGeometry/Canonical/ClosureDrazinBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **1**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ClosureDrazinBridge.lean` | `advisory` | 7 | 0 | 1 | 5 | 6 |

## Findings by file

### `lean/InfoGeometry/Canonical/ClosureDrazinBridge.lean`
- module: `InfoGeometry.Canonical.ClosureDrazinBridge`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L19 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L34 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L34 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L182 [advisory] `existential-packaging` in `theorem exists_drazinInverse_of_constructiveClosure` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L213 [advisory] `existential-packaging` in `theorem exists_constructiveClosureDrazinData` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

