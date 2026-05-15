# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:44.695333+00:00`
Root: `lean/InfoGeometry/Canonical/BohmMadelungOperatorialBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **22**
- Hard: **0**
- Soft: **18**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/BohmMadelungOperatorialBridge.lean` | `advisory` | 40 | 0 | 18 | 4 | 22 |

## Findings by file

### `lean/InfoGeometry/Canonical/BohmMadelungOperatorialBridge.lean`
- module: `InfoGeometry.Canonical.BohmMadelungOperatorialBridge`
- status: `advisory`
- debt_score: `40`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L36 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L37 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L59 [soft] `skeletal-proof` in `theorem stateGeneratorField_phaseReadout_eq_metric_comp_complex_i` — proof appears to close via minimal tactic one-liner
  - L69 [soft] `skeletal-proof` in `theorem stateGeneratorField_phaseReadout_eq_metric_comp_K` — proof appears to close via minimal tactic one-liner
  - L93 [soft] `simp-law-injection` in `simp-declaration constantStateGeneratorField_generator_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L96 [soft] `simp-law-injection` in `simp-declaration constantStateGeneratorField_relativeModularGenerator_eq_modularTransportGenerator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L98 [soft] `skeletal-proof` in `theorem constantStateGeneratorField_relativeModularGenerator_eq_modularTransportGenerator` — proof appears to close via minimal tactic one-liner
  - L107 [soft] `simp-law-injection` in `simp-declaration constantStateGeneratorField_stateInducedDerivation_eq_relativeModularDeriv` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L109 [soft] `skeletal-proof` in `theorem constantStateGeneratorField_stateInducedDerivation_eq_relativeModularDeriv` — proof appears to close via minimal tactic one-liner
  - L116 [soft] `simp-law-injection` in `simp-declaration constantStateGeneratorField_stateGaugeGenerator_eq_phaseLinearPart` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L118 [soft] `skeletal-proof` in `theorem constantStateGeneratorField_stateGaugeGenerator_eq_phaseLinearPart` — proof appears to close via minimal tactic one-liner
  - L127 [soft] `simp-law-injection` in `simp-declaration constantStateGeneratorField_stateSourceGenerator_eq_phaseAntilinearPart` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L129 [soft] `skeletal-proof` in `theorem constantStateGeneratorField_stateSourceGenerator_eq_phaseAntilinearPart` — proof appears to close via minimal tactic one-liner
  - L138 [soft] `simp-law-injection` in `simp-declaration constantStateGeneratorField_stateGaugeDerivation_eq_transportCommutator_phaseLinearPart` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L140 [soft] `skeletal-proof` in `theorem constantStateGeneratorField_stateGaugeDerivation_eq_transportCommutator_phaseLinearPart` — proof appears to close via minimal tactic one-liner
  - L148 [soft] `simp-law-injection` in `simp-declaration constantStateGeneratorField_stateSourceDerivation_eq_transportCommutator_phaseAntilinearPart` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L150 [soft] `skeletal-proof` in `theorem constantStateGeneratorField_stateSourceDerivation_eq_transportCommutator_phaseAntilinearPart` — proof appears to close via minimal tactic one-liner
  - L173 [soft] `simp-law-injection` in `simp-declaration constantStateGeneratorField_stateQGTReadout_apply_eq_metricPhase_relativeModularDeriv` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L175 [soft] `skeletal-proof` in `theorem constantStateGeneratorField_stateQGTReadout_apply_eq_metricPhase_relativeModularDeriv` — proof appears to close via minimal tactic one-liner
  - L259 [soft] `skeletal-proof` in `theorem potentialDatum_constantStateGeneratorField_stateQGTReadout_pair_eq_comparisonReadout_pair` — proof appears to close via minimal tactic one-liner

