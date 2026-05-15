# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:04.595468+00:00`
Root: `lean/InfoGeometry/Canonical/SuperchargeTransportBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **17**
- Hard: **0**
- Soft: **14**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SuperchargeTransportBridge.lean` | `advisory` | 31 | 0 | 14 | 3 | 17 |

## Findings by file

### `lean/InfoGeometry/Canonical/SuperchargeTransportBridge.lean`
- module: `InfoGeometry.Canonical.SuperchargeTransportBridge`
- status: `advisory`
- debt_score: `31`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L37 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L57 [soft] `simp-law-injection` in `simp-declaration transportedParitySupercharge_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L62 [soft] `simp-law-injection` in `simp-declaration transportedModularSupercharge_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L70 [soft] `skeletal-proof` in `theorem parity_modular_anticommutator_eq_zero` — proof appears to close via minimal tactic one-liner
  - L84 [soft] `skeletal-proof` in `theorem deriv_transportedParitySupercharge` — proof appears to close via minimal tactic one-liner
  - L97 [soft] `skeletal-proof` in `theorem deriv_transportedModularSupercharge` — proof appears to close via minimal tactic one-liner
  - L114 [soft] `skeletal-proof` in `theorem deriv_transportedParitySupercharge_at_zero_eq_phaseAntilinear_of_commute_phaseLinearPart` — proof appears to close via minimal tactic one-liner
  - L134 [soft] `skeletal-proof` in `theorem deriv_transportedModularSupercharge_at_zero_eq_phaseAntilinear_of_commute_phaseLinearPart` — proof appears to close via minimal tactic one-liner
  - L150 [soft] `skeletal-proof` in `theorem deriv2_transportedParitySupercharge_at_zero_eq_operatorInformationHessian` — proof appears to close via minimal tactic one-liner
  - L163 [soft] `skeletal-proof` in `theorem deriv2_transportedParitySupercharge_at_zero_eq_operatorInformationMetricPart` — proof appears to close via minimal tactic one-liner
  - L176 [soft] `skeletal-proof` in `theorem deriv2_transportedParitySupercharge_at_zero_eq_metricPart_add_half_curvaturePart` — proof appears to close via minimal tactic one-liner
  - L196 [soft] `skeletal-proof` in `theorem deriv_anticommutator_transportedParity_staticModular_at_zero` — proof appears to close via minimal tactic one-liner
  - L386 [soft] `skeletal-proof` in `theorem quasilatticeTranslationCandidate_eq_hoppingSeed` — proof appears to close via minimal tactic one-liner
  - L398 [soft] `skeletal-proof` in `theorem quasilatticeTranslationCandidate_eq_phaseLinearSeed_add_phaseAntilinearSeed` — proof appears to close via minimal tactic one-liner
  - L412 [soft] `skeletal-proof` in `theorem quasilatticeTranslationCandidate_eq_phaseAntilinearSeed_of_commute_phaseLinearPart` — proof appears to close via minimal tactic one-liner

