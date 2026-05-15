# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:26.502111+00:00`
Root: `lean/InfoGeometry/Dynamics/UnruhKMS.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **6**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Dynamics/UnruhKMS.lean` | `advisory` | 15 | 0 | 6 | 3 | 9 |

## Findings by file

### `lean/InfoGeometry/Dynamics/UnruhKMS.lean`
- module: `InfoGeometry.Dynamics.UnruhKMS`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L28 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L30 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L49 [soft] `skeletal-proof` in `theorem boostGenerator_eq_modularSign` — proof appears to close via minimal tactic one-liner
  - L65 [soft] `skeletal-proof` in `theorem modularHamiltonian_eq_modularSign` — proof appears to close via minimal tactic one-liner
  - L68 [soft] `simp-law-injection` in `simp-declaration modularHamiltonian_sq_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L75 [soft] `simp-law-injection` in `simp-declaration phaseGenerator_eq_modular_j_comp_boostGenerator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L82 [soft] `simp-law-injection` in `simp-declaration boostGenerator_eq_modular_j_comp_phaseGenerator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L98 [soft] `simp-law-injection` in `simp-declaration unruhFlow_is_modular_flow` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

