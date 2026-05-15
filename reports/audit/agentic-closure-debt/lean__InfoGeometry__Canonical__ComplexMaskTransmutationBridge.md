# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:54.771726+00:00`
Root: `lean/InfoGeometry/Canonical/ComplexMaskTransmutationBridge.lean`
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
| `lean/InfoGeometry/Canonical/ComplexMaskTransmutationBridge.lean` | `advisory` | 11 | 0 | 4 | 3 | 7 |

## Findings by file

### `lean/InfoGeometry/Canonical/ComplexMaskTransmutationBridge.lean`
- module: `InfoGeometry.Canonical.ComplexMaskTransmutationBridge`
- status: `advisory`
- debt_score: `11`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L37 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L67 [soft] `skeletal-proof` in `theorem canonicalModularSeed_eq_neg_superHamiltonian_comp_lorentzBivectorGenerator` — proof appears to close via minimal tactic one-liner
  - L80 [soft] `skeletal-proof` in `theorem superHamiltonian_eq_modularTransportGenerator_lorentzBivectorSeed_transmuted` — proof appears to close via minimal tactic one-liner
  - L95 [soft] `skeletal-proof` in `theorem lorentzBivectorGenerator_maps_plusSheet_to_minusSheet` — proof appears to close via minimal tactic one-liner
  - L106 [soft] `skeletal-proof` in `theorem lorentzBivectorGenerator_maps_minusSheet_to_plusSheet` — proof appears to close via minimal tactic one-liner

