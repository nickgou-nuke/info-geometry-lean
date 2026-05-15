# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:50.871175+00:00`
Root: `lean/InfoGeometry/Krein/ExponentialIsometry.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **4**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Krein/ExponentialIsometry.lean` | `advisory` | 15 | 0 | 4 | 7 | 11 |

## Findings by file

### `lean/InfoGeometry/Krein/ExponentialIsometry.lean`
- module: `InfoGeometry.Krein.ExponentialIsometry`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L30 [soft] `skeletal-proof` in `lemma kreinAdjoint_eq_jUnit_conj` — proof appears to close via minimal tactic one-liner
  - L34 [soft] `skeletal-proof` in `lemma exp_kreinAdjoint` — proof appears to close via minimal tactic one-liner
  - L40 [advisory] `local-hypothesis-injection` in `lemma exp_kreinAdjoint` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L42 [advisory] `local-hypothesis-injection` in `lemma exp_kreinAdjoint` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L55 [advisory] `local-hypothesis-injection` in `theorem exp_preservesMetric` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L57 [advisory] `local-hypothesis-injection` in `theorem exp_preservesMetric` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L60 [advisory] `local-hypothesis-injection` in `theorem exp_preservesMetric` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L63 [advisory] `local-hypothesis-injection` in `theorem exp_preservesMetric` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L74 [soft] `simp-law-injection` in `simp-declaration expAutomorphism_toContinuousLinearMap` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L77 [soft] `skeletal-proof` in `theorem expAutomorphism_preservesMetric` — proof appears to close via minimal tactic one-liner

