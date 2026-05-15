# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:44.774722+00:00`
Root: `lean/InfoGeometry/SuperMetriplectic/UnifiedOwnerEntropyBridge.lean`
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
| `lean/InfoGeometry/SuperMetriplectic/UnifiedOwnerEntropyBridge.lean` | `advisory` | 7 | 0 | 1 | 5 | 6 |

## Findings by file

### `lean/InfoGeometry/SuperMetriplectic/UnifiedOwnerEntropyBridge.lean`
- module: `InfoGeometry.SuperMetriplectic.UnifiedOwnerEntropyBridge`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L31 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L33 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L45 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L45 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L83 [advisory] `bridge-shaped-declaration` in `theorem ownerEntropyBridge_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

