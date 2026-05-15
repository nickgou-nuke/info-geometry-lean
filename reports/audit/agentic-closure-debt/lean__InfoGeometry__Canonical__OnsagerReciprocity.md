# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:34.461821+00:00`
Root: `lean/InfoGeometry/Canonical/OnsagerReciprocity.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **24**
- Hard: **0**
- Soft: **21**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/OnsagerReciprocity.lean` | `advisory` | 45 | 0 | 21 | 3 | 24 |

## Findings by file

### `lean/InfoGeometry/Canonical/OnsagerReciprocity.lean`
- module: `InfoGeometry.Canonical.OnsagerReciprocity`
- status: `advisory`
- debt_score: `45`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L41 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L43 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L59 [soft] `simp-law-injection` in `simp-declaration operatorSecondVariationForm_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L66 [soft] `simp-law-injection` in `simp-declaration operatorSecondVariationForm_eq_probe_observableLieHessian` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L95 [soft] `simp-law-injection` in `simp-declaration operatorMetricHessianForm_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L102 [soft] `simp-law-injection` in `simp-declaration operatorCurvatureHessianForm_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L109 [soft] `simp-law-injection` in `simp-declaration operatorPhaseHessianForm_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L115 [soft] `simp-law-injection` in `simp-declaration operatorPhaseHessianForm_eq_metric_comp_channelPhaseAxis` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L121 [soft] `simp-law-injection` in `simp-declaration operatorMetricHessianForm_swap` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L129 [soft] `simp-law-injection` in `simp-declaration operatorCurvatureHessianForm_swap_neg` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L136 [soft] `simp-law-injection` in `simp-declaration operatorMetricHessianForm_diag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L152 [soft] `skeletal-proof` in `theorem operatorMetricHessianForm_eq_half_probe_observableLieHessian_add_swap` — proof appears to close via minimal tactic one-liner
  - L161 [soft] `simp-law-injection` in `simp-declaration operatorCurvatureHessianForm_diag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L181 [soft] `skeletal-proof` in `theorem responseCoefficient_swap` — proof appears to close via minimal tactic one-liner
  - L212 [soft] `skeletal-proof` in `theorem curvatureCoefficient_swap_neg` — proof appears to close via minimal tactic one-liner
  - L236 [soft] `skeletal-proof` in `theorem channelCorrelationAtState_swap` — proof appears to close via minimal tactic one-liner
  - L245 [soft] `skeletal-proof` in `theorem comparisonGeneratorMetric_swap` — proof appears to close via minimal tactic one-liner
  - L258 [soft] `skeletal-proof` in `theorem comparisonGeneratorPhase_swap_neg_of_IsPhaseLinear` — proof appears to close via minimal tactic one-liner
  - L301 [soft] `skeletal-proof` in `theorem toRelationalInformationDatum_comparisonTransportGenerator_eq_gauge_add_source` — proof appears to close via minimal tactic one-liner
  - L312 [soft] `simp-law-injection` in `simp-declaration toRelationalInformationDatum_comparisonGaugeGenerator_eq_phaseLinearPart` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L314 [soft] `skeletal-proof` in `theorem toRelationalInformationDatum_comparisonGaugeGenerator_eq_phaseLinearPart` — proof appears to close via minimal tactic one-liner
  - L324 [soft] `simp-law-injection` in `simp-declaration toRelationalInformationDatum_comparisonSourceGenerator_eq_phaseAntilinearPart` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L326 [soft] `skeletal-proof` in `theorem toRelationalInformationDatum_comparisonSourceGenerator_eq_phaseAntilinearPart` — proof appears to close via minimal tactic one-liner

