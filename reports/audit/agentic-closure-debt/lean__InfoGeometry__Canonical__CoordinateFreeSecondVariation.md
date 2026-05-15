# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:56.763866+00:00`
Root: `lean/InfoGeometry/Canonical/CoordinateFreeSecondVariation.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **16**
- Hard: **0**
- Soft: **12**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/CoordinateFreeSecondVariation.lean` | `advisory` | 28 | 0 | 12 | 4 | 16 |

## Findings by file

### `lean/InfoGeometry/Canonical/CoordinateFreeSecondVariation.lean`
- module: `InfoGeometry.Canonical.CoordinateFreeSecondVariation`
- status: `advisory`
- debt_score: `28`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L42 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L44 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L45 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L46 [soft] `simp-law-injection` in `simp-declaration operatorInformationCurvaturePart_self_eq_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L49 [soft] `skeletal-proof` in `theorem operatorInformationCurvaturePart_self_eq_zero` — proof appears to close via minimal tactic one-liner
  - L54 [soft] `simp-law-injection` in `simp-declaration operatorInformationHessian_eq_metricPart_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L68 [soft] `simp-law-injection` in `simp-declaration modularCurvatureOperator_eq_metricPart_phaseAxis` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L74 [soft] `skeletal-proof` in `theorem modularCurvatureOperator_eq_metricPart_phaseAxis` — proof appears to close via minimal tactic one-liner
  - L80 [soft] `simp-law-injection` in `simp-declaration modularCurvatureOperator_eq_metricPart_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L91 [soft] `simp-law-injection` in `simp-declaration comparisonState_metric_phase_pair_eq_correlation_pair` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L110 [soft] `simp-law-injection` in `simp-declaration toRelationalInformationDatum_metric_phase_pair_eq_correlation_pair` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L135 [soft] `simp-law-injection` in `simp-declaration comparisonMetricPhaseReadout_pair_eq_operator_pair` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L155 [soft] `simp-law-injection` in `simp-declaration toRelationalInformationDatum_comparisonMetricPhaseReadout_pair_eq_operator_pair` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L180 [soft] `simp-law-injection` in `simp-declaration comparisonMetricPhaseReadout_pair_eq_gauge_source_operator_pair` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L207 [soft] `simp-law-injection` in `simp-declaration toRelationalInformationDatum_comparisonMetricPhaseReadout_pair_eq_gauge_source_operator_pair` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

