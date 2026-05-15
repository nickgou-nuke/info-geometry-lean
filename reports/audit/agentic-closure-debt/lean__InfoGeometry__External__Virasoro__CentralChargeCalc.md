# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:30.777915+00:00`
Root: `lean/InfoGeometry/External/Virasoro/CentralChargeCalc.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **17**
- Hard: **0**
- Soft: **12**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/External/Virasoro/CentralChargeCalc.lean` | `advisory` | 29 | 0 | 12 | 5 | 17 |

## Findings by file

### `lean/InfoGeometry/External/Virasoro/CentralChargeCalc.lean`
- module: `InfoGeometry.External.Virasoro.CentralChargeCalc`
- status: `advisory`
- debt_score: `29`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L56 [soft] `simp-law-injection` in `simp-declaration zPrimitive_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L60 [soft] `simp-law-injection` in `simp-declaration zPrimitive_apply_of_nonneg` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L65 [soft] `simp-law-injection` in `simp-declaration zPrimitive_apply_of_nonpos` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L72 [soft] `simp-law-injection` in `simp-declaration zPrimitive_succ` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L78 [advisory] `local-hypothesis-injection` in `def zPrimitive` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L87 [advisory] `local-hypothesis-injection` in `lemma eq_zPrimitive_of_eq_zero_of_forall_eq_add` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L92 [advisory] `local-hypothesis-injection` in `lemma eq_zPrimitive_of_eq_zero_of_forall_eq_add` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L149 [soft] `skeletal-proof` in `lemma zMonomialF_eq` — proof appears to close via minimal tactic one-liner
  - L175 [soft] `skeletal-proof` in `lemma zMonomialF_zero_eq` — proof appears to close via minimal tactic one-liner
  - L179 [soft] `skeletal-proof` in `lemma zMonomialF_one_eq` — proof appears to close via minimal tactic one-liner
  - L183 [soft] `skeletal-proof` in `lemma zMonomialF_two_eq` — proof appears to close via minimal tactic one-liner
  - L187 [soft] `skeletal-proof` in `lemma zMonomialF_three_eq` — proof appears to close via minimal tactic one-liner
  - L191 [soft] `skeletal-proof` in `lemma zMonomialF_four_eq` — proof appears to close via minimal tactic one-liner
  - L195 [soft] `skeletal-proof` in `lemma zMonomialF_five_eq` — proof appears to close via minimal tactic one-liner
  - L199 [soft] `skeletal-proof` in `lemma zMonomialF_apply_eq_zero_of_of_nonneg_lt` — proof appears to close via minimal tactic one-liner
  - L208 [advisory] `local-hypothesis-injection` in `lemma bosonic_sugawara_cc_calc` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

