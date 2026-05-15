# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:39.378364+00:00`
Root: `lean/InfoGeometry/Canonical/OperatorialInformationLift.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **0**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/OperatorialInformationLift.lean` | `advisory` | 6 | 0 | 0 | 6 | 6 |

## Findings by file

### `lean/InfoGeometry/Canonical/OperatorialInformationLift.lean`
- module: `InfoGeometry.Canonical.OperatorialInformationLift`
- status: `advisory`
- debt_score: `6`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L74 [advisory] `local-hypothesis-injection` in `theorem normalized_logOperatorialInformationLift_modularHamiltonian` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L111 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L113 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L143 [advisory] `existential-packaging` in `theorem transportedDiracOperatorialInformationLift_of_strictSymmetry` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L190 [advisory] `existential-packaging` in `theorem transportedThermalOperatorialInformationLift_of_strictSymmetry` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

