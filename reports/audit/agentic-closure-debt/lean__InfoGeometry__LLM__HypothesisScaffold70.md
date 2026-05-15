# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:56.187868+00:00`
Root: `lean/InfoGeometry/LLM/HypothesisScaffold70.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **0**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/LLM/HypothesisScaffold70.lean` | `advisory` | 5 | 0 | 0 | 5 | 5 |

## Findings by file

### `lean/InfoGeometry/LLM/HypothesisScaffold70.lean`
- module: `InfoGeometry.LLM.HypothesisScaffold70`
- status: `advisory`
- debt_score: `5`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L55 [advisory] `existential-packaging` in `theorem h70_krein_energy_surface` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L70 [advisory] `existential-packaging` in `theorem h70_kms_softmax_normalization` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L89 [advisory] `bridge-shaped-declaration` in `theorem h70_router_free_energy_bridge` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L89 [advisory] `existential-packaging` in `theorem h70_router_free_energy_bridge` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

