# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:49.499636+00:00`
Root: `lean/InfoGeometry/Canonical/CentralChargeAnomaly.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **4**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/CentralChargeAnomaly.lean` | `advisory` | 10 | 0 | 4 | 2 | 6 |

## Findings by file

### `lean/InfoGeometry/Canonical/CentralChargeAnomaly.lean`
- module: `InfoGeometry.Canonical.CentralChargeAnomaly`
- status: `advisory`
- debt_score: `10`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L36 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L52 [soft] `skeletal-proof` in `theorem centralCharge_eq_transport_slice` — proof appears to close via minimal tactic one-liner
  - L120 [soft] `skeletal-proof` in `theorem isAnomalyFree_iff_transportSlice_eq_zero_of_canonicalMultiplet` — proof appears to close via minimal tactic one-liner
  - L150 [soft] `skeletal-proof` in `theorem isAnomalyFree_iff_centralCharge_eq_zero_of_canonicalMultiplet` — proof appears to close via minimal tactic one-liner
  - L173 [soft] `skeletal-proof` in `theorem transportSlice_ne_zero_of_centralCharge_ne_zero` — proof appears to close via minimal tactic one-liner

