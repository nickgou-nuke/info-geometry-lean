# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:05.715932+00:00`
Root: `lean/InfoGeometry/Canonical/ThermodynamicGenerator.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **29**
- Hard: **0**
- Soft: **22**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ThermodynamicGenerator.lean` | `advisory` | 51 | 0 | 22 | 7 | 29 |

## Findings by file

### `lean/InfoGeometry/Canonical/ThermodynamicGenerator.lean`
- module: `InfoGeometry.Canonical.ThermodynamicGenerator`
- status: `advisory`
- debt_score: `51`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L40 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L42 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L55 [soft] `simp-law-injection` in `simp-declaration souriauTemperatureVector_eq_generator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L59 [soft] `simp-law-injection` in `simp-declaration souriauTemperatureVector_eq_transportGenerator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L65 [soft] `simp-law-injection` in `simp-declaration souriauTemperatureVector_eq_stateRelativeModularGenerator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L78 [soft] `simp-law-injection` in `simp-declaration operatorialGibbsWeight_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L83 [soft] `simp-law-injection` in `simp-declaration apply_operatorialGibbsWeight_eq_informationPartitionFunction` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L89 [soft] `skeletal-proof` in `theorem apply_operatorialGibbsWeight_eq_informationPartitionFunction` — proof appears to close via minimal tactic one-liner
  - L102 [soft] `skeletal-proof` in `theorem hasDerivAt_apply_operatorialGibbsWeight_zero` — proof appears to close via minimal tactic one-liner
  - L121 [soft] `simp-law-injection` in `simp-declaration firstVariation_eq_probe_stateInducedDynamics` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L124 [soft] `skeletal-proof` in `theorem firstVariation_eq_probe_stateInducedDynamics` — proof appears to close via minimal tactic one-liner
  - L139 [soft] `simp-law-injection` in `simp-declaration comparisonReadout_pair_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L145 [soft] `skeletal-proof` in `theorem comparisonReadout_pair_apply` — proof appears to close via minimal tactic one-liner
  - L156 [soft] `simp-law-injection` in `simp-declaration toRelationalInformationDatum_comparisonMetricPhase_pair_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L252 [soft] `skeletal-proof` in `theorem comparisonReadout_pair_eq_zero_of_isPotentialKillingOperator` — proof appears to close via minimal tactic one-liner
  - L348 [soft] `skeletal-proof` in `theorem isPotentialKillingOperator_iff_isThermodynamicReadoutStationary` — proof appears to close via minimal tactic one-liner
  - L444 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L446 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L481 [soft] `simp-law-injection` in `simp-declaration apply_operatorialGrandCanonicalWeight_eq_informationPartitionFunction` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L483 [soft] `skeletal-proof` in `theorem apply_operatorialGrandCanonicalWeight_eq_informationPartitionFunction` — proof appears to close via minimal tactic one-liner
  - L500 [soft] `skeletal-proof` in `theorem operatorialGrandCanonicalMassieuPotential_normalizedInfinitesimalLaw` — proof appears to close via minimal tactic one-liner
  - L540 [soft] `skeletal-proof` in `theorem stateRelativeGrandCanonicalGenerator_eq_generator_of_zeroChemicalPotential` — proof appears to close via minimal tactic one-liner
  - L581 [soft] `skeletal-proof` in `theorem stateRelativeGrandCanonicalGenerator_eq_generator_of_vacuumTransported` — proof appears to close via minimal tactic one-liner
  - L658 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L660 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L705 [soft] `skeletal-proof` in `theorem liftedChiralAnomalyMassieuPotential_normalizedInfinitesimalLaw` — proof appears to close via minimal tactic one-liner
  - L718 [soft] `skeletal-proof` in `theorem liftedProjectorObstructionMassieuPotential_normalizedInfinitesimalLaw` — proof appears to close via minimal tactic one-liner
  - L731 [soft] `skeletal-proof` in `theorem liftedEinsteinAnomalyMassieuPotential_normalizedInfinitesimalLaw` — proof appears to close via minimal tactic one-liner

