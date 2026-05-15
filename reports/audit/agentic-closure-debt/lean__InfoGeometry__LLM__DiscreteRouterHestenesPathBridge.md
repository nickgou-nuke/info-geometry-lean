# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:56.028725+00:00`
Root: `lean/InfoGeometry/LLM/DiscreteRouterHestenesPathBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **2**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/LLM/DiscreteRouterHestenesPathBridge.lean` | `advisory` | 8 | 0 | 2 | 4 | 6 |

## Findings by file

### `lean/InfoGeometry/LLM/DiscreteRouterHestenesPathBridge.lean`
- module: `InfoGeometry.LLM.DiscreteRouterHestenesPathBridge`
- status: `advisory`
- debt_score: `8`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L19 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L21 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L42 [soft] `skeletal-proof` in `theorem pathGibbsRouterUpdate_eq_softmax_shift` — proof appears to close via minimal tactic one-liner
  - L85 [advisory] `existential-packaging` in `theorem pathSurprisalLogits_exp_beta_one` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L102 [soft] `skeletal-proof` in `theorem bayesRouterUpdate_eq_pathGibbsRouterUpdate_of_energy_match` — proof appears to close via minimal tactic one-liner

