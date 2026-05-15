# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:40.506880+00:00`
Root: `lean/InfoGeometry/Canonical/ArnoldNetworkPresentation.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **6**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ArnoldNetworkPresentation.lean` | `advisory` | 14 | 0 | 6 | 2 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/ArnoldNetworkPresentation.lean`
- module: `InfoGeometry.Canonical.ArnoldNetworkPresentation`
- status: `advisory`
- debt_score: `14`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L44 [soft] `skeletal-proof` in `theorem arnoldMetricReadout_nonneg` — proof appears to close via minimal tactic one-liner
  - L68 [soft] `skeletal-proof` in `theorem toQuantumPresentation_generator_eq_arnold` — proof appears to close via minimal tactic one-liner
  - L80 [soft] `skeletal-proof` in `theorem arnoldGenerator_totalCost_le_of_contract` — proof appears to close via minimal tactic one-liner
  - L115 [soft] `skeletal-proof` in `theorem toQuantumPresentation_generator_totalCost_le_of_contract` — proof appears to close via minimal tactic one-liner
  - L130 [soft] `skeletal-proof` in `theorem arnoldGenerator_mem_submodule` — proof appears to close via minimal tactic one-liner
  - L149 [advisory] `existential-packaging` in `theorem arnoldGenerator_eq_of_experts_fix` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L149 [soft] `skeletal-proof` in `theorem arnoldGenerator_eq_of_experts_fix` — proof appears to close via minimal tactic one-liner

