# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:08.630575+00:00`
Root: `lean/InfoGeometry/Canonical/UnifiedSuperchargeOddOddBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **2**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/UnifiedSuperchargeOddOddBridge.lean` | `advisory` | 9 | 0 | 2 | 5 | 7 |

## Findings by file

### `lean/InfoGeometry/Canonical/UnifiedSuperchargeOddOddBridge.lean`
- module: `InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge`
- status: `advisory`
- debt_score: `9`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L37 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L39 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L51 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L51 [soft] `section-law-variable` in `variable U` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L119 [soft] `skeletal-proof` in `theorem oddOddBracket_eq_translation_plus_central_plus_defectResidual` — proof appears to close via minimal tactic one-liner
  - L157 [advisory] `bridge-shaped-declaration` in `theorem toOddOddDecompositionData_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

