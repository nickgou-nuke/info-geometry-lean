# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:51.349018+00:00`
Root: `lean/InfoGeometry/Canonical/RelativeModularPotential.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **22**
- Hard: **0**
- Soft: **19**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RelativeModularPotential.lean` | `advisory` | 41 | 0 | 19 | 3 | 22 |

## Findings by file

### `lean/InfoGeometry/Canonical/RelativeModularPotential.lean`
- module: `InfoGeometry.Canonical.RelativeModularPotential`
- status: `advisory`
- debt_score: `41`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L36 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L38 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L44 [soft] `law-field-locker` in `structure-field PotentialDatum.probe` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L107 [soft] `simp-law-injection` in `simp-declaration comparisonMetricReadout_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L115 [soft] `simp-law-injection` in `simp-declaration comparisonPhaseReadout_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L168 [soft] `simp-law-injection` in `simp-declaration generator_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L172 [soft] `simp-law-injection` in `simp-declaration modularSeed_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L176 [soft] `simp-law-injection` in `simp-declaration transportGenerator_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L182 [soft] `simp-law-injection` in `simp-declaration value_eq_probe_generator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L196 [soft] `simp-law-injection` in `simp-declaration comparisonPhaseReadout_eq_metric_comp_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L205 [soft] `simp-law-injection` in `simp-declaration comparisonPhaseReadout_eq_metric_comp_modularComplexI` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L214 [soft] `simp-law-injection` in `simp-declaration channelCorrelationAtState_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L218 [soft] `simp-law-injection` in `simp-declaration comparisonStateGeneratorMetric_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L224 [soft] `simp-law-injection` in `simp-declaration comparisonStateGeneratorPhase_apply_eq_comp_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L233 [soft] `simp-law-injection` in `simp-declaration comparisonStateGeneratorPhase_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L243 [soft] `simp-law-injection` in `simp-declaration toRelationalInformationDatum_informationFunctional` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L249 [soft] `simp-law-injection` in `simp-declaration toRelationalInformationDatum_firstVariation` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L255 [soft] `simp-law-injection` in `simp-declaration toRelationalInformationDatum_functionalShift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L262 [soft] `simp-law-injection` in `simp-declaration toRelationalInformationDatum_comparisonGeneratorMetric_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L271 [soft] `simp-law-injection` in `simp-declaration toRelationalInformationDatum_comparisonGeneratorPhase_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L284 [soft] `simp-law-injection` in `simp-declaration toRelationalInformationDatum_comparisonGeneratorPhase_apply_eq_comp_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

