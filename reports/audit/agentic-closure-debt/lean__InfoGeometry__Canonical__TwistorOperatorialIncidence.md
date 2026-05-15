# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:07.546784+00:00`
Root: `lean/InfoGeometry/Canonical/TwistorOperatorialIncidence.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **0**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/TwistorOperatorialIncidence.lean` | `advisory` | 5 | 0 | 0 | 5 | 5 |

## Findings by file

### `lean/InfoGeometry/Canonical/TwistorOperatorialIncidence.lean`
- module: `InfoGeometry.Canonical.TwistorOperatorialIncidence`
- status: `advisory`
- debt_score: `5`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L13 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L15 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L51 [advisory] `local-hypothesis-injection` in `theorem operatorialIncidence_iff_projectorObstructionOperator_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L57 [advisory] `local-hypothesis-injection` in `theorem operatorialIncidence_iff_projectorObstructionOperator_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

