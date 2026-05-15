# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:13.407381+00:00`
Root: `lean/InfoGeometry/Canonical/HestenesAnalyticity.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **16**
- Hard: **0**
- Soft: **5**
- Advisory: **11**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/HestenesAnalyticity.lean` | `advisory` | 21 | 0 | 5 | 11 | 16 |

## Findings by file

### `lean/InfoGeometry/Canonical/HestenesAnalyticity.lean`
- module: `InfoGeometry.Canonical.HestenesAnalyticity`
- status: `advisory`
- debt_score: `21`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L41 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L43 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L44 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L45 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L46 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L47 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L63 [soft] `skeletal-proof` in `theorem id_isHestenesHolomorphicDifferential` — proof appears to close via minimal tactic one-liner
  - L86 [soft] `skeletal-proof` in `theorem holomorphicDifferential_comp` — proof appears to close via minimal tactic one-liner
  - L105 [soft] `skeletal-proof` in `theorem antiholomorphicDifferential_comp_antiholomorphic` — proof appears to close via minimal tactic one-liner
  - L131 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L133 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L147 [soft] `skeletal-proof` in `theorem hestenesAnalyticSymmetry_commutator` — proof appears to close via minimal tactic one-liner
  - L196 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L198 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L223 [soft] `skeletal-proof` in `theorem virasoro_central_bracket_zero` — proof appears to close via minimal tactic one-liner

