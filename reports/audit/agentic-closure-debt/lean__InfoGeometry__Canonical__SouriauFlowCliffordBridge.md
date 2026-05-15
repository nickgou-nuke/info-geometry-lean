# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:56.969574+00:00`
Root: `lean/InfoGeometry/Canonical/SouriauFlowCliffordBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **5**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SouriauFlowCliffordBridge.lean` | `advisory` | 13 | 0 | 5 | 3 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/SouriauFlowCliffordBridge.lean`
- module: `InfoGeometry.Canonical.SouriauFlowCliffordBridge`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L28 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L30 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L37 [soft] `skeletal-proof` in `theorem souriau_fockCommutator_eq_two_smul_lieProduct` — proof appears to close via minimal tactic one-liner
  - L52 [soft] `skeletal-proof` in `theorem souriau_fockAnticommutator_eq_two_smul_jordanProduct` — proof appears to close via minimal tactic one-liner
  - L67 [soft] `skeletal-proof` in `theorem souriau_comp_eq_jordan_plus_lie` — proof appears to close via minimal tactic one-liner
  - L88 [soft] `skeletal-proof` in `theorem deriv_apply_operatorialGibbsWeight_zero_eq_neg_expectation_souriau` — proof appears to close via minimal tactic one-liner
  - L123 [soft] `skeletal-proof` in `theorem sourceSink_souriau_defect_split_of_connection_eq` — proof appears to close via minimal tactic one-liner

