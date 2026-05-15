# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:23.959096+00:00`
Root: `lean/InfoGeometry/Core/Entropy.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **10**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Core/Entropy.lean` | `advisory` | 21 | 0 | 10 | 1 | 11 |

## Findings by file

### `lean/InfoGeometry/Core/Entropy.lean`
- module: `InfoGeometry.Core.Entropy`
- status: `advisory`
- debt_score: `21`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L16 [soft] `simp-law-injection` in `simp-declaration logDensity_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L19 [soft] `simp-law-injection` in `simp-declaration surprisal_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L26 [soft] `simp-law-injection` in `simp-declaration entropy_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L29 [soft] `simp-law-injection` in `simp-declaration expectation_const` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L53 [soft] `simp-law-injection` in `simp-declaration expectation_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L57 [soft] `simp-law-injection` in `simp-declaration expectation_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L67 [soft] `simp-law-injection` in `simp-declaration klDiv_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L70 [soft] `simp-law-injection` in `simp-declaration klDiv_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L74 [soft] `skeletal-proof` in `lemma klDiv_eq_zero_iff_toMeasure_eq` — proof appears to close via minimal tactic one-liner
  - L79 [soft] `simp-law-injection` in `simp-declaration fin_kl_div_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

