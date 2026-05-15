# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:35.900630+00:00`
Root: `lean/InfoGeometry/Canonical/OperatorFenchelRegularCone.lean`
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
| `lean/InfoGeometry/Canonical/OperatorFenchelRegularCone.lean` | `advisory` | 7 | 0 | 1 | 5 | 6 |

## Findings by file

### `lean/InfoGeometry/Canonical/OperatorFenchelRegularCone.lean`
- module: `InfoGeometry.Canonical.OperatorFenchelRegularCone`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L34 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L49 [soft] `simp-law-injection` in `simp-declaration mem_regularPositiveConeOmegaD_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L111 [advisory] `local-hypothesis-injection` in `theorem operatorFenchelYoung_on_doubledKrein` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L127 [advisory] `bridge-shaped-declaration` in `theorem operatorLegendreHessianInverse_packet_of_continuousLinearEquiv` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

