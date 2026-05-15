# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:34.684068+00:00`
Root: `lean/InfoGeometry/Quantum/GeometricTensorTest.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **6**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Quantum/GeometricTensorTest.lean` | `advisory` | 17 | 0 | 6 | 5 | 11 |

## Findings by file

### `lean/InfoGeometry/Quantum/GeometricTensorTest.lean`
- module: `InfoGeometry.Quantum.GeometricTensorTest`
- status: `advisory`
- debt_score: `17`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L16 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L18 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L19 [soft] `skeletal-proof` in `theorem ofMajorana_g_eq_metric` — proof appears to close via minimal tactic one-liner
  - L30 [advisory] `bridge-shaped-declaration` in `theorem ofMajorana_compat` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L43 [advisory] `bridge-shaped-declaration` in `theorem ofMajorana_compat_complex_i` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L101 [soft] `skeletal-proof` in `theorem qgtOfOperator_KRotation_metric_and_berry_invariant` — proof appears to close via minimal tactic one-liner
  - L123 [soft] `skeletal-proof` in `theorem kreinQgtOfOperator_KRotation_metric_and_berry_invariant` — proof appears to close via minimal tactic one-liner
  - L142 [soft] `skeletal-proof` in `theorem qgtOfOperator_modularTransportFlow_metric_and_berry_invariant_of_commute_generator` — proof appears to close via minimal tactic one-liner
  - L170 [soft] `skeletal-proof` in `theorem qgtOfOperator_modularTransportFlow_metric_and_berry_invariant_of_generator_eq_smul_phaseAxis` — proof appears to close via minimal tactic one-liner
  - L199 [soft] `skeletal-proof` in `theorem kreinQgtOfOperator_modularTransportFlow_metric_and_berry_invariant_of_generator_eq_smul_phaseAxis` — proof appears to close via minimal tactic one-liner

