# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:57.534577+00:00`
Root: `lean/InfoGeometry/LLM/ScalarThermoBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **3**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/LLM/ScalarThermoBridge.lean` | `advisory` | 11 | 0 | 3 | 5 | 8 |

## Findings by file

### `lean/InfoGeometry/LLM/ScalarThermoBridge.lean`
- module: `InfoGeometry.LLM.ScalarThermoBridge`
- status: `advisory`
- debt_score: `11`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L60 [advisory] `existential-packaging` in `theorem convex_softmax_routerLogits_add_uniformShift` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L60 [soft] `skeletal-proof` in `theorem convex_softmax_routerLogits_add_uniformShift` — proof appears to close via minimal tactic one-liner
  - L100 [advisory] `existential-packaging` in `theorem normalizedWeights_eq_analytic_logSumExpWeight` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L126 [advisory] `bridge-shaped-declaration` in `theorem switchMatrix_mem_rowStochastic_bridge` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L126 [soft] `skeletal-proof` in `theorem switchMatrix_mem_rowStochastic_bridge` — proof appears to close via minimal tactic one-liner
  - L139 [advisory] `bridge-shaped-declaration` in `theorem fenchelGap_nonneg_bridge` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L139 [soft] `skeletal-proof` in `theorem fenchelGap_nonneg_bridge` — proof appears to close via minimal tactic one-liner

