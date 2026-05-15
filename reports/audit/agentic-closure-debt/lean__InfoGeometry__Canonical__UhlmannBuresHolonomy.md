# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:08.222858+00:00`
Root: `lean/InfoGeometry/Canonical/UhlmannBuresHolonomy.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **5**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/UhlmannBuresHolonomy.lean` | `advisory` | 16 | 0 | 5 | 6 | 11 |

## Findings by file

### `lean/InfoGeometry/Canonical/UhlmannBuresHolonomy.lean`
- module: `InfoGeometry.Canonical.UhlmannBuresHolonomy`
- status: `advisory`
- debt_score: `16`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L10 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L10 [soft] `section-law-variable` in `variable c` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L11 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L28 [soft] `skeletal-proof` in `theorem chi_zero_iff_alignment` — proof appears to close via minimal tactic one-liner
  - L50 [soft] `skeletal-proof` in `theorem zero_curvature_of_inertial_regular_lane` — proof appears to close via minimal tactic one-liner
  - L53 [advisory] `local-hypothesis-injection` in `theorem zero_curvature_of_inertial_regular_lane` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L61 [soft] `skeletal-proof` in `theorem zero_defect_scattering_of_inertial_regular_lane` — proof appears to close via minimal tactic one-liner
  - L76 [soft] `skeletal-proof` in `theorem curvature_eq_neg_defectScattering_of_inertial_regular_lane` — proof appears to close via minimal tactic one-liner
  - L79 [advisory] `local-hypothesis-injection` in `theorem curvature_eq_neg_defectScattering_of_inertial_regular_lane` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L81 [advisory] `local-hypothesis-injection` in `theorem curvature_eq_neg_defectScattering_of_inertial_regular_lane` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

