# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:37.528565+00:00`
Root: `lean/InfoGeometry/Canonical/OperatorThermoBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **4**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/OperatorThermoBridge.lean` | `advisory` | 11 | 0 | 4 | 3 | 7 |

## Findings by file

### `lean/InfoGeometry/Canonical/OperatorThermoBridge.lean`
- module: `InfoGeometry.Canonical.OperatorThermoBridge`
- status: `advisory`
- debt_score: `11`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L29 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L31 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L55 [soft] `skeletal-proof` in `theorem operatorCanonicalFreeEnergyReadout_eq_massieu` — proof appears to close via minimal tactic one-liner
  - L77 [soft] `skeletal-proof` in `theorem scalarCanonicalFreeEnergy_sign` — proof appears to close via minimal tactic one-liner
  - L83 [soft] `skeletal-proof` in `theorem scalarCanonicalEntropy_sign` — proof appears to close via minimal tactic one-liner
  - L89 [soft] `skeletal-proof` in `theorem scalarCanonicalEnergy_sign` — proof appears to close via minimal tactic one-liner

