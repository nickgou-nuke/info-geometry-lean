# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:55.876400+00:00`
Root: `lean/InfoGeometry/LLM/DiscreteRouterBayesStep.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **2**
- Hard: **0**
- Soft: **1**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/LLM/DiscreteRouterBayesStep.lean` | `advisory` | 3 | 0 | 1 | 1 | 2 |

## Findings by file

### `lean/InfoGeometry/LLM/DiscreteRouterBayesStep.lean`
- module: `InfoGeometry.LLM.DiscreteRouterBayesStep`
- status: `advisory`
- debt_score: `3`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L25 [soft] `skeletal-proof` in `theorem bayes_router_update_preserves_simplex` — proof appears to close via minimal tactic one-liner

