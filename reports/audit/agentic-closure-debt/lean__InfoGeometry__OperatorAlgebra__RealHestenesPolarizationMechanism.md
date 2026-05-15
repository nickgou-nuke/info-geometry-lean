# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:21.374602+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/RealHestenesPolarizationMechanism.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **8**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/RealHestenesPolarizationMechanism.lean` | `advisory` | 21 | 0 | 8 | 5 | 13 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/RealHestenesPolarizationMechanism.lean`
- module: `InfoGeometry.OperatorAlgebra.RealHestenesPolarizationMechanism`
- status: `advisory`
- debt_score: `21`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L34 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L35 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L125 [soft] `simp-law-injection` in `simp-declaration chiralityPolarization_is_J` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L130 [soft] `skeletal-proof` in `theorem chiralityPolarization_is_J` — proof appears to close via minimal tactic one-liner
  - L134 [soft] `simp-law-injection` in `simp-declaration chiralityPolarization_plus_is_weylPlus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L139 [soft] `skeletal-proof` in `theorem chiralityPolarization_plus_is_weylPlus` — proof appears to close via minimal tactic one-liner
  - L143 [soft] `simp-law-injection` in `simp-declaration chiralityPolarization_minus_is_weylMinus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L148 [soft] `skeletal-proof` in `theorem chiralityPolarization_minus_is_weylMinus` — proof appears to close via minimal tactic one-liner
  - L284 [advisory] `existential-packaging` in `def RealHestenesPolarizationMechanismTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L301 [soft] `simp-law-injection` in `simp-declaration diagonalShadowGuard_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L311 [soft] `simp-law-injection` in `simp-declaration realOnlyGuard_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

