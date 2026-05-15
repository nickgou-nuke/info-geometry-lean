# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:11.111941+00:00`
Root: `lean/InfoGeometry/Canonical/GlobalChiralDecomposition.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **2**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/GlobalChiralDecomposition.lean` | `advisory` | 7 | 0 | 2 | 3 | 5 |

## Findings by file

### `lean/InfoGeometry/Canonical/GlobalChiralDecomposition.lean`
- module: `InfoGeometry.Canonical.GlobalChiralDecomposition`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L20 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L22 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L52 [soft] `skeletal-proof` in `theorem activeApex_decomposition_projector_form_of_commute` — proof appears to close via minimal tactic one-liner
  - L87 [soft] `skeletal-proof` in `theorem chiralRangeDomain_decomposition` — proof appears to close via minimal tactic one-liner

