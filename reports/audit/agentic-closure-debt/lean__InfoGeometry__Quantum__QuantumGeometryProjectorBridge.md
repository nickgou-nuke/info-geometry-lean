# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:35.999711+00:00`
Root: `lean/InfoGeometry/Quantum/QuantumGeometryProjectorBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **16**
- Hard: **0**
- Soft: **13**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Quantum/QuantumGeometryProjectorBridge.lean` | `advisory` | 29 | 0 | 13 | 3 | 16 |

## Findings by file

### `lean/InfoGeometry/Quantum/QuantumGeometryProjectorBridge.lean`
- module: `InfoGeometry.Quantum.QuantumGeometryProjectorBridge`
- status: `advisory`
- debt_score: `29`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L24 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L26 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L40 [soft] `simp-law-injection` in `simp-declaration fst_quantumGeometryProjectorOperatorPair` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L47 [soft] `simp-law-injection` in `simp-declaration snd_quantumGeometryProjectorOperatorPair` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L54 [soft] `simp-law-injection` in `simp-declaration plusProjectorFlux_fst_quantumGeometryProjectorOperatorPair` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L62 [soft] `simp-law-injection` in `simp-declaration minusProjectorFlux_fst_quantumGeometryProjectorOperatorPair` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L70 [soft] `simp-law-injection` in `simp-declaration plusProjectorFlux_snd_quantumGeometryProjectorOperatorPair` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L82 [soft] `simp-law-injection` in `simp-declaration minusProjectorFlux_snd_quantumGeometryProjectorOperatorPair` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L94 [soft] `skeletal-proof` in `theorem weldedProjectorObstructionStatePhaseReadout_eq_metricOfOperator_snd_quantumGeometryProjectorOperatorPair_of_projectorAgreement` — proof appears to close via minimal tactic one-liner
  - L152 [soft] `skeletal-proof` in `theorem deriv_fst_quantumGeometryEinsteinTransportedOperatorPair_at_zero_eq_relativeModularDeriv` — proof appears to close via minimal tactic one-liner
  - L197 [soft] `skeletal-proof` in `theorem deriv_snd_quantumGeometryEinsteinTransportedOperatorPair_at_zero_eq_relativeModularSourceDeriv_of_commute_gaugePart` — proof appears to close via minimal tactic one-liner
  - L360 [soft] `skeletal-proof` in `theorem metricOfOperator_self_eq_comparisonStateGeneratorMetric_id` — proof appears to close via minimal tactic one-liner
  - L372 [soft] `skeletal-proof` in `theorem berryOfOperator_self_eq_comparisonStateGeneratorPhase_id` — proof appears to close via minimal tactic one-liner
  - L535 [soft] `skeletal-proof` in `theorem metricOfOperator_dualSheetLift_quantumGeometryOp_eq_twoStateChannelCorrelation_id` — proof appears to close via minimal tactic one-liner
  - L599 [soft] `skeletal-proof` in `theorem deriv_comparisonTransportPhaseShiftedChannelCorrelation_liftedProjectorObstructionCorrelationSeed_at_zero_eq_comparisonMetricReadout_snd_quantumGeometryProjectorOperatorPair` — proof appears to close via minimal tactic one-liner

