# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:39.243823+00:00`
Root: `lean/InfoGeometry/Canonical/OperatorialHessianBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **12**
- Hard: **0**
- Soft: **3**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/OperatorialHessianBridge.lean` | `advisory` | 15 | 0 | 3 | 9 | 12 |

## Findings by file

### `lean/InfoGeometry/Canonical/OperatorialHessianBridge.lean`
- module: `InfoGeometry.Canonical.OperatorialHessianBridge`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L36 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L55 [soft] `skeletal-proof` in `theorem hasDerivAt_scalarLogReadout_zero` — proof appears to close via minimal tactic one-liner
  - L62 [advisory] `local-hypothesis-injection` in `theorem hasDerivAt_scalarLogReadout_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L69 [advisory] `local-hypothesis-injection` in `theorem hasDerivAt_scalarLogReadout_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L89 [soft] `skeletal-proof` in `theorem hasDerivAt_scalarTransportReadout` — proof appears to close via minimal tactic one-liner
  - L195 [advisory] `local-hypothesis-injection` in `theorem deriv2_scalarLogReadout_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L209 [advisory] `local-hypothesis-injection` in `theorem deriv2_scalarLogReadout_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L214 [advisory] `local-hypothesis-injection` in `theorem deriv2_scalarLogReadout_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L219 [advisory] `local-hypothesis-injection` in `theorem deriv2_scalarLogReadout_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L232 [soft] `skeletal-proof` in `theorem deriv2_scalarLogReadout_zero_eq_probe_operatorInformationHessian_of_stationary` — proof appears to close via minimal tactic one-liner

