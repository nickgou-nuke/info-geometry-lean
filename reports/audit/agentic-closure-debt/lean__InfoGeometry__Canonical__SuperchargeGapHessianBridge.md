# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:03.922929+00:00`
Root: `lean/InfoGeometry/Canonical/SuperchargeGapHessianBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **3**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SuperchargeGapHessianBridge.lean` | `advisory` | 9 | 0 | 3 | 3 | 6 |

## Findings by file

### `lean/InfoGeometry/Canonical/SuperchargeGapHessianBridge.lean`
- module: `InfoGeometry.Canonical.SuperchargeGapHessianBridge`
- status: `advisory`
- debt_score: `9`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L36 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L38 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L50 [soft] `skeletal-proof` in `theorem transportedParityModularGapSeed_eq_cpt_lane_transportSeed` — proof appears to close via minimal tactic one-liner
  - L65 [soft] `skeletal-proof` in `theorem deriv2_transportedParitySupercharge_at_zero_eq_metricPart_add_half_curvaturePart_cpt_lane` — proof appears to close via minimal tactic one-liner
  - L243 [soft] `skeletal-proof` in `theorem root_supercharge_lichnerowicz_closure` — proof appears to close via minimal tactic one-liner

