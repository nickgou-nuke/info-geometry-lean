# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:04.280126+00:00`
Root: `lean/InfoGeometry/Canonical/DrazinModularSingularityBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **1**
- Advisory: **10**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DrazinModularSingularityBridge.lean` | `advisory` | 12 | 0 | 1 | 10 | 11 |

## Findings by file

### `lean/InfoGeometry/Canonical/DrazinModularSingularityBridge.lean`
- module: `InfoGeometry.Canonical.DrazinModularSingularityBridge`
- status: `advisory`
- debt_score: `12`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L34 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L165 [advisory] `local-hypothesis-injection` in `theorem certified_operator_ratio_regularization_corridor` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L166 [advisory] `local-hypothesis-injection` in `theorem certified_operator_ratio_regularization_corridor` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L195 [advisory] `local-hypothesis-injection` in `theorem certified_operator_ratio_regularization_kills_defect_of_alignment` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L196 [advisory] `local-hypothesis-injection` in `theorem certified_operator_ratio_regularization_kills_defect_of_alignment` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L276 [soft] `skeletal-proof` in `theorem modularAdjointFlow_eq_self_of_commute_flow` — proof appears to close via minimal tactic one-liner
  - L281 [advisory] `local-hypothesis-injection` in `theorem modularAdjointFlow_eq_self_of_commute_flow` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L291 [advisory] `local-hypothesis-injection` in `theorem modularAdjointFlow_eq_self_of_commute_flow` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L306 [advisory] `local-hypothesis-injection` in `theorem modularAdjointFlow_eq_self_of_commute_generator` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

