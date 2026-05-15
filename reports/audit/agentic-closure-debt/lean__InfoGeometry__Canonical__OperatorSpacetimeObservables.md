# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:37.122424+00:00`
Root: `lean/InfoGeometry/Canonical/OperatorSpacetimeObservables.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **18**
- Hard: **0**
- Soft: **4**
- Advisory: **14**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/OperatorSpacetimeObservables.lean` | `advisory` | 22 | 0 | 4 | 14 | 18 |

## Findings by file

### `lean/InfoGeometry/Canonical/OperatorSpacetimeObservables.lean`
- module: `InfoGeometry.Canonical.OperatorSpacetimeObservables`
- status: `advisory`
- debt_score: `22`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L27 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L29 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L30 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L31 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L32 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L33 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L34 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L35 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L68 [soft] `skeletal-proof` in `theorem idObservable_eq_lightconePlus_add_lightconeMinus` — proof appears to close via minimal tactic one-liner
  - L76 [soft] `skeletal-proof` in `theorem epsilonObservable_eq_lightconePlus_sub_lightconeMinus` — proof appears to close via minimal tactic one-liner
  - L79 [advisory] `local-hypothesis-injection` in `theorem epsilonObservable_eq_lightconePlus_sub_lightconeMinus` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L99 [soft] `skeletal-proof` in `theorem lightconePlus_eq_half_id_add_epsilon` — proof appears to close via minimal tactic one-liner
  - L102 [advisory] `local-hypothesis-injection` in `theorem lightconePlus_eq_half_id_add_epsilon` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L103 [advisory] `local-hypothesis-injection` in `theorem lightconePlus_eq_half_id_add_epsilon` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L117 [soft] `skeletal-proof` in `theorem lightconeMinus_eq_half_id_sub_epsilon` — proof appears to close via minimal tactic one-liner
  - L120 [advisory] `local-hypothesis-injection` in `theorem lightconeMinus_eq_half_id_sub_epsilon` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L121 [advisory] `local-hypothesis-injection` in `theorem lightconeMinus_eq_half_id_sub_epsilon` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

