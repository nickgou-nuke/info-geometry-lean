# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:34.082152+00:00`
Root: `lean/InfoGeometry/Quantum/FiniteEntanglementComplexityCore.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **12**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Quantum/FiniteEntanglementComplexityCore.lean` | `advisory` | 25 | 0 | 12 | 1 | 13 |

## Findings by file

### `lean/InfoGeometry/Quantum/FiniteEntanglementComplexityCore.lean`
- module: `InfoGeometry.Quantum.FiniteEntanglementComplexityCore`
- status: `advisory`
- debt_score: `25`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L159 [soft] `skeletal-proof` in `theorem copyBobToCharlie_b_eq_c` — proof appears to close via minimal tactic one-liner
  - L190 [soft] `simp-law-injection` in `simp-declaration hammingWeight_simpleString` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L193 [soft] `skeletal-proof` in `theorem hammingWeight_simpleString` — proof appears to close via minimal tactic one-liner
  - L243 [soft] `simp-law-injection` in `simp-declaration classicalSingleFlipComplexity_simple` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L246 [soft] `skeletal-proof` in `theorem classicalSingleFlipComplexity_simple` — proof appears to close via minimal tactic one-liner
  - L294 [soft] `simp-law-injection` in `simp-declaration cost_nil` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L299 [soft] `skeletal-proof` in `theorem cost_nil` — proof appears to close via minimal tactic one-liner
  - L302 [soft] `simp-law-injection` in `simp-declaration cost_singleton` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L307 [soft] `skeletal-proof` in `theorem cost_singleton` — proof appears to close via minimal tactic one-liner
  - L311 [soft] `skeletal-proof` in `theorem cost_append_gate` — proof appears to close via minimal tactic one-liner
  - L320 [soft] `skeletal-proof` in `theorem cost_append` — proof appears to close via minimal tactic one-liner
  - L341 [soft] `skeletal-proof` in `theorem cost_eq_length` — proof appears to close via minimal tactic one-liner

