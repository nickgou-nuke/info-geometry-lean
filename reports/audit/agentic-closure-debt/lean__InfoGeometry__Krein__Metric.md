# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:53.497354+00:00`
Root: `lean/InfoGeometry/Krein/Metric.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **1**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Krein/Metric.lean` | `advisory` | 9 | 0 | 1 | 7 | 8 |

## Findings by file

### `lean/InfoGeometry/Krein/Metric.lean`
- module: `InfoGeometry.Krein.Metric`
- status: `advisory`
- debt_score: `9`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L37 [advisory] `local-hypothesis-injection` in `lemma one_div_sqrt_two_sq_metric` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L53 [soft] `skeletal-proof` in `lemma hessian_indefinite_formCoord_eq_hessianDoubled` — proof appears to close via minimal tactic one-liner
  - L62 [advisory] `local-hypothesis-injection` in `lemma hessian_indefinite_formCoord_eq_hessianDoubled` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L73 [advisory] `local-hypothesis-injection` in `lemma hessian_indefinite_formCoord_eq_hessianDoubled` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L81 [advisory] `local-hypothesis-injection` in `lemma hessian_indefinite_formCoord_eq_hessianDoubled` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L91 [advisory] `local-hypothesis-injection` in `lemma hessian_indefinite_formCoord_eq_hessianDoubled` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L98 [advisory] `local-hypothesis-injection` in `lemma hessian_indefinite_formCoord_eq_hessianDoubled` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

