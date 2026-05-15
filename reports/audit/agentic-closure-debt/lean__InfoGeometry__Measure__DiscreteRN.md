# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:01.121821+00:00`
Root: `lean/InfoGeometry/Measure/DiscreteRN.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **3**
- Advisory: **10**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Measure/DiscreteRN.lean` | `advisory` | 16 | 0 | 3 | 10 | 13 |

## Findings by file

### `lean/InfoGeometry/Measure/DiscreteRN.lean`
- module: `InfoGeometry.Measure.DiscreteRN`
- status: `advisory`
- debt_score: `16`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L20 [soft] `skeletal-proof` in `lemma set_lintegral_singleton` — proof appears to close via minimal tactic one-liner
  - L38 [soft] `skeletal-proof` in `theorem rnDeriv_eq_div_of_singleton` — proof appears to close via minimal tactic one-liner
  - L47 [advisory] `local-hypothesis-injection` in `theorem rnDeriv_eq_div_of_singleton` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L57 [advisory] `local-hypothesis-injection` in `theorem rnDeriv_eq_div_of_singleton` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L63 [soft] `skeletal-proof` in `theorem rnDeriv_pmf_eq_div` — proof appears to close via minimal tactic one-liner
  - L81 [advisory] `local-hypothesis-injection` in `theorem rnDeriv_pmf_eq_div` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L83 [advisory] `local-hypothesis-injection` in `theorem rnDeriv_pmf_eq_div` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L85 [advisory] `local-hypothesis-injection` in `theorem rnDeriv_pmf_eq_div` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L86 [advisory] `local-hypothesis-injection` in `theorem rnDeriv_pmf_eq_div` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L89 [advisory] `local-hypothesis-injection` in `theorem rnDeriv_pmf_eq_div` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L91 [advisory] `local-hypothesis-injection` in `theorem rnDeriv_pmf_eq_div` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L93 [advisory] `local-hypothesis-injection` in `theorem rnDeriv_pmf_eq_div` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

