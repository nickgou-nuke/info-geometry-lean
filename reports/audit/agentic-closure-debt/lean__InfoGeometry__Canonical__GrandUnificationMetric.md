# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:12.894146+00:00`
Root: `lean/InfoGeometry/Canonical/GrandUnificationMetric.lean`
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
| `lean/InfoGeometry/Canonical/GrandUnificationMetric.lean` | `advisory` | 9 | 0 | 2 | 5 | 7 |

## Findings by file

### `lean/InfoGeometry/Canonical/GrandUnificationMetric.lean`
- module: `InfoGeometry.Canonical.GrandUnificationMetric`
- status: `advisory`
- debt_score: `9`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L33 [soft] `skeletal-proof` in `theorem metric_symmetry_of_metricPositive` — proof appears to close via minimal tactic one-liner
  - L57 [soft] `skeletal-proof` in `theorem bregman_local_second_order_of_logDet` — proof appears to close via minimal tactic one-liner
  - L77 [advisory] `local-hypothesis-injection` in `theorem bregman_local_second_order_of_logDet` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L80 [advisory] `local-hypothesis-injection` in `theorem bregman_local_second_order_of_logDet` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L82 [advisory] `local-hypothesis-injection` in `theorem bregman_local_second_order_of_logDet` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L94 [advisory] `local-hypothesis-injection` in `theorem bregman_local_second_order_of_logDet` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

