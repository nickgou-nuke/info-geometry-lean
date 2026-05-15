# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:49.903463+00:00`
Root: `lean/InfoGeometry/Canonical/RelationalInformationDynamics.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **40**
- Hard: **0**
- Soft: **34**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RelationalInformationDynamics.lean` | `advisory` | 74 | 0 | 34 | 6 | 40 |

## Findings by file

### `lean/InfoGeometry/Canonical/RelationalInformationDynamics.lean`
- module: `InfoGeometry.Canonical.RelationalInformationDynamics`
- status: `advisory`
- debt_score: `74`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L36 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L38 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L61 [soft] `simp-law-injection` in `simp-declaration operatorExponentialChart_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L62 [soft] `skeletal-proof` in `theorem operatorExponentialChart_zero` — proof appears to close via minimal tactic one-liner
  - L68 [soft] `skeletal-proof` in `theorem hasDerivAt_operatorExponentialChart_zero` — proof appears to close via minimal tactic one-liner
  - L96 [soft] `simp-law-injection` in `simp-declaration operatorLogGeneratingPotential_eq_operatorMassieuPotential` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L105 [soft] `simp-law-injection` in `simp-declaration informationPartitionFunction_eq_exponentialChart_readout` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L107 [soft] `skeletal-proof` in `theorem informationPartitionFunction_eq_exponentialChart_readout` — proof appears to close via minimal tactic one-liner
  - L133 [soft] `skeletal-proof` in `theorem operatorMassieuPotential_normalizedInfinitesimalLaw` — proof appears to close via minimal tactic one-liner
  - L171 [soft] `simp-law-injection` in `simp-declaration observableLieDerivation_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L276 [soft] `simp-law-injection` in `simp-declaration observableLieHessian_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L301 [soft] `skeletal-proof` in `theorem operatorInformationHessian_eq_double_transportCommutator` — proof appears to close via minimal tactic one-liner
  - L394 [soft] `skeletal-proof` in `theorem operatorInformationCurvaturePart_eq_bracketDerivation` — proof appears to close via minimal tactic one-liner
  - L441 [soft] `skeletal-proof` in `theorem hasDerivAt_transportedMassieuExpectation_zero` — proof appears to close via minimal tactic one-liner
  - L465 [advisory] `local-hypothesis-injection` in `theorem hasDerivAt_transportedMassieuExpectation_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L511 [soft] `skeletal-proof` in `theorem observableLieDerivation_transport_intertwines` — proof appears to close via minimal tactic one-liner
  - L543 [soft] `skeletal-proof` in `theorem operatorMassieuExpectation_transport_intertwines_firstVariation` — proof appears to close via minimal tactic one-liner
  - L560 [soft] `skeletal-proof` in `theorem operatorMassieuExpectation_transport_intertwines_hessian` — proof appears to close via minimal tactic one-liner
  - L607 [soft] `simp-law-injection` in `simp-declaration channelMetricAtState_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L617 [soft] `simp-law-injection` in `simp-declaration channelEvalAtState_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L636 [soft] `simp-law-injection` in `simp-declaration channelKreinMetricAtState_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L661 [soft] `simp-law-injection` in `simp-declaration constructiveRelationalDatum_informationFunctional` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L667 [soft] `skeletal-proof` in `theorem constructiveRelationalDatum_informationFunctional` — proof appears to close via minimal tactic one-liner
  - L676 [soft] `simp-law-injection` in `simp-declaration constructiveRelationalDatum_referenceFunctionalValue` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L682 [soft] `skeletal-proof` in `theorem constructiveRelationalDatum_referenceFunctionalValue` — proof appears to close via minimal tactic one-liner
  - L691 [soft] `simp-law-injection` in `simp-declaration constructiveRelationalDatum_comparisonFunctionalValue` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L697 [soft] `skeletal-proof` in `theorem constructiveRelationalDatum_comparisonFunctionalValue` — proof appears to close via minimal tactic one-liner
  - L706 [soft] `simp-law-injection` in `simp-declaration constructiveRelationalDatum_comparisonGeneratorMetric_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L709 [soft] `skeletal-proof` in `theorem constructiveRelationalDatum_comparisonGeneratorMetric_apply` — proof appears to close via minimal tactic one-liner
  - L719 [soft] `simp-law-injection` in `simp-declaration constructiveRelationalDatum_firstVariation_comparison` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L722 [soft] `skeletal-proof` in `theorem constructiveRelationalDatum_firstVariation_comparison` — proof appears to close via minimal tactic one-liner
  - L732 [soft] `simp-law-injection` in `simp-declaration constructiveRelationalDatum_comparisonGeneratorPhase_apply_eq_comp_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L735 [soft] `skeletal-proof` in `theorem constructiveRelationalDatum_comparisonGeneratorPhase_apply_eq_comp_complex_i` — proof appears to close via minimal tactic one-liner
  - L747 [soft] `simp-law-injection` in `simp-declaration constructiveRelationalDatum_comparisonGeneratorPhase_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L768 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L770 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L781 [soft] `simp-law-injection` in `simp-declaration operatorInformationPhaseReadout_eq_metric_comp_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L793 [soft] `simp-law-injection` in `simp-declaration operatorInformationPhaseReadout_eq_metric_comp_modularComplexI` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L795 [soft] `skeletal-proof` in `theorem operatorInformationPhaseReadout_eq_metric_comp_modularComplexI` — proof appears to close via minimal tactic one-liner

