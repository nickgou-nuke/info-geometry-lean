# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:03.412716+00:00`
Root: `lean/InfoGeometry/Canonical/SuperchargeCARCCRBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **19**
- Hard: **0**
- Soft: **18**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SuperchargeCARCCRBridge.lean` | `advisory` | 37 | 0 | 18 | 1 | 19 |

## Findings by file

### `lean/InfoGeometry/Canonical/SuperchargeCARCCRBridge.lean`
- module: `InfoGeometry.Canonical.SuperchargeCARCCRBridge`
- status: `advisory`
- debt_score: `37`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L29 [soft] `simp-law-injection` in `simp-declaration fockEndomorphism_eq_doubledEnd` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L37 [soft] `simp-law-injection` in `simp-declaration paritySuperchargeOp_eq_modular_j` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L44 [soft] `simp-law-injection` in `simp-declaration modularSuperchargeOp_eq_spectral_epsilon` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L52 [soft] `simp-law-injection` in `simp-declaration cptSuperchargeOp_eq_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L59 [soft] `simp-law-injection` in `simp-declaration cptSuperchargeOp_eq_modular_j_comp_spectral_epsilon` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L82 [soft] `skeletal-proof` in `theorem parity_modular_supercharge_car_zero` — proof appears to close via minimal tactic one-liner
  - L93 [soft] `skeletal-proof` in `theorem modular_j_spectral_epsilon_car_zero` — proof appears to close via minimal tactic one-liner
  - L102 [soft] `skeletal-proof` in `theorem parity_modular_supercharge_ccr_eq_two_cpt` — proof appears to close via minimal tactic one-liner
  - L117 [soft] `skeletal-proof` in `theorem parity_modular_supercharge_ccrBracket_eq_two_cpt` — proof appears to close via minimal tactic one-liner
  - L127 [soft] `skeletal-proof` in `theorem modular_j_spectral_epsilon_ccr_eq_two_complex_i` — proof appears to close via minimal tactic one-liner
  - L132 [soft] `simp-law-injection` in `simp-declaration cptSuperchargeOp_eq_dilationOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L137 [soft] `simp-law-injection` in `simp-declaration cptSuperchargeOp_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L145 [soft] `simp-law-injection` in `simp-declaration complex_i_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L163 [soft] `skeletal-proof` in `theorem complex_i_maps_plus_to_minus` — proof appears to close via minimal tactic one-liner
  - L178 [soft] `skeletal-proof` in `theorem complex_i_maps_minus_to_plus` — proof appears to close via minimal tactic one-liner
  - L182 [soft] `simp-law-injection` in `simp-declaration carBracket_swap` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L189 [soft] `simp-law-injection` in `simp-declaration ccrBracket_swap` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L209 [soft] `skeletal-proof` in `theorem concrete_car_pair` — proof appears to close via minimal tactic one-liner

