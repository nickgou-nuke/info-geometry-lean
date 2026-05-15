# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:59.973301+00:00`
Root: `lean/InfoGeometry/MaxEnt/IProjection.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **20**
- Hard: **0**
- Soft: **2**
- Advisory: **18**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/MaxEnt/IProjection.lean` | `advisory` | 22 | 0 | 2 | 18 | 20 |

## Findings by file

### `lean/InfoGeometry/MaxEnt/IProjection.lean`
- module: `InfoGeometry.MaxEnt.IProjection`
- status: `advisory`
- debt_score: `22`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L17 [soft] `skeletal-proof` in `lemma integrable_of_fintype` — proof appears to close via minimal tactic one-liner
  - L29 [advisory] `local-hypothesis-injection` in `lemma integrable_of_fintype` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L41 [soft] `skeletal-proof` in `theorem toReal_klDiv_eq_sum_log_ratio` — proof appears to close via minimal tactic one-liner
  - L62 [advisory] `local-hypothesis-injection` in `theorem toReal_klDiv_eq_sum_log_ratio` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L65 [advisory] `local-hypothesis-injection` in `theorem toReal_klDiv_eq_sum_log_ratio` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L93 [advisory] `existential-packaging` in `theorem gibbs_is_minimizer` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L114 [advisory] `local-hypothesis-injection` in `theorem gibbs_is_minimizer` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L120 [advisory] `local-hypothesis-injection` in `theorem gibbs_is_minimizer` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L124 [advisory] `local-hypothesis-injection` in `theorem gibbs_is_minimizer` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L128 [advisory] `local-hypothesis-injection` in `theorem gibbs_is_minimizer` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L135 [advisory] `existential-packaging` in `theorem gibbs_is_unique_minimizer` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L157 [advisory] `local-hypothesis-injection` in `theorem gibbs_is_unique_minimizer` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L161 [advisory] `local-hypothesis-injection` in `theorem gibbs_is_unique_minimizer` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L170 [advisory] `local-hypothesis-injection` in `theorem gibbs_is_unique_minimizer` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L172 [advisory] `local-hypothesis-injection` in `theorem gibbs_is_unique_minimizer` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L179 [advisory] `local-hypothesis-injection` in `theorem gibbs_is_unique_minimizer` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L195 [advisory] `local-hypothesis-injection` in `theorem gibbs_is_unique_minimizer` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L201 [advisory] `local-hypothesis-injection` in `theorem gibbs_is_unique_minimizer` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L208 [advisory] `local-hypothesis-injection` in `theorem gibbs_is_unique_minimizer` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

