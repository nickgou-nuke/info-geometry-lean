# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:04.463110+00:00`
Root: `lean/InfoGeometry/Canonical/SuperchargeRoleBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **15**
- Hard: **0**
- Soft: **12**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SuperchargeRoleBridge.lean` | `advisory` | 27 | 0 | 12 | 3 | 15 |

## Findings by file

### `lean/InfoGeometry/Canonical/SuperchargeRoleBridge.lean`
- module: `InfoGeometry.Canonical.SuperchargeRoleBridge`
- status: `advisory`
- debt_score: `27`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L36 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L38 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L44 [soft] `simp-law-injection` in `simp-declaration transportedParitySupercharge_zero_eq_paritySuperchargeOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L50 [soft] `simp-law-injection` in `simp-declaration transportedParitySupercharge_zero_eq_modular_j` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L56 [soft] `simp-law-injection` in `simp-declaration transportedModularSupercharge_zero_eq_modularSuperchargeOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L62 [soft] `simp-law-injection` in `simp-declaration transportedModularSupercharge_zero_eq_spectral_epsilon` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L75 [soft] `skeletal-proof` in `theorem transportedParityModularGapSeed_eq_car_of_infinitesimalParitySupercharge` — proof appears to close via minimal tactic one-liner
  - L87 [soft] `skeletal-proof` in `theorem transportedParityModularGapSeed_eq_car_root` — proof appears to close via minimal tactic one-liner
  - L102 [soft] `skeletal-proof` in `theorem transportedParityModularGapSeed_eq_phaseAntilinearCAR_of_commute_phaseLinearPart` — proof appears to close via minimal tactic one-liner
  - L120 [soft] `skeletal-proof` in `theorem transportedParityModularGapSeed_eq_phaseAntilinearCAR_root_of_commute_phaseLinearPart` — proof appears to close via minimal tactic one-liner
  - L141 [soft] `skeletal-proof` in `theorem deriv2_transportedParitySupercharge_at_zero_eq_operatorInformationHessian_of_paritySuperchargeOp` — proof appears to close via minimal tactic one-liner
  - L154 [soft] `skeletal-proof` in `theorem deriv2_transportedParitySupercharge_at_zero_eq_operatorInformationHessian_of_modular_j` — proof appears to close via minimal tactic one-liner
  - L170 [soft] `skeletal-proof` in `theorem deriv2_transportedParitySupercharge_at_zero_eq_metricPart_add_half_curvaturePart_of_paritySuperchargeOp` — proof appears to close via minimal tactic one-liner
  - L186 [soft] `skeletal-proof` in `theorem deriv2_transportedParitySupercharge_at_zero_eq_metricPart_add_half_curvaturePart_of_modular_j` — proof appears to close via minimal tactic one-liner

