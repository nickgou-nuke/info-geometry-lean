# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:29.718296+00:00`
Root: `lean/InfoGeometry/Canonical/ModularKramersBridge.lean`
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
| `lean/InfoGeometry/Canonical/ModularKramersBridge.lean` | `advisory` | 11 | 0 | 4 | 3 | 7 |

## Findings by file

### `lean/InfoGeometry/Canonical/ModularKramersBridge.lean`
- module: `InfoGeometry.Canonical.ModularKramersBridge`
- status: `advisory`
- debt_score: `11`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L30 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L32 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L54 [soft] `skeletal-proof` in `theorem kramers_preserves_modularConjugation_fixed_of_commute` — proof appears to close via minimal tactic one-liner
  - L72 [soft] `skeletal-proof` in `theorem kramers_preserves_modularFlow_fixed_of_commute` — proof appears to close via minimal tactic one-liner
  - L123 [soft] `skeletal-proof` in `theorem majoranaFix_preserved_under_modularFlow_of_commute_C` — proof appears to close via minimal tactic one-liner
  - L163 [soft] `skeletal-proof` in `theorem modularConjugation_equivariant_kramersPair_of_commute` — proof appears to close via minimal tactic one-liner

