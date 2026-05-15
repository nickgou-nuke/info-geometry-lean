# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:21.891754+00:00`
Root: `lean/InfoGeometry/Convex/Duality.lean`
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
| `lean/InfoGeometry/Convex/Duality.lean` | `advisory` | 11 | 0 | 3 | 5 | 8 |

## Findings by file

### `lean/InfoGeometry/Convex/Duality.lean`
- module: `InfoGeometry.Convex.Duality`
- status: `advisory`
- debt_score: `11`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L20 [soft] `simp-law-injection` in `simp-declaration bregman_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L27 [soft] `skeletal-proof` in `lemma KL_param_eq_bregman_swap` — proof appears to close via minimal tactic one-liner
  - L50 [advisory] `local-hypothesis-injection` in `lemma bregman_nonneg_of_convex_at` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L63 [advisory] `local-hypothesis-injection` in `lemma bregman_nonneg_of_convex_at` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L65 [advisory] `local-hypothesis-injection` in `lemma bregman_nonneg_of_convex_at` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L73 [advisory] `local-hypothesis-injection` in `lemma bregman_nonneg_of_convex_at` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L89 [soft] `skeletal-proof` in `lemma KL_param_nonneg_of_convex_at` — proof appears to close via minimal tactic one-liner

