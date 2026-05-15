# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:02.218022+00:00`
Root: `lean/InfoGeometry/Canonical/StateDependentTransport.lean`
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
| `lean/InfoGeometry/Canonical/StateDependentTransport.lean` | `advisory` | 31 | 0 | 14 | 3 | 17 |

## Findings by file

### `lean/InfoGeometry/Canonical/StateDependentTransport.lean`
- module: `InfoGeometry.Canonical.StateDependentTransport`
- status: `advisory`
- debt_score: `31`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L22 [soft] `law-field-locker` in `structure-field StateModularDatum.modularSeed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L40 [soft] `law-field-locker` in `structure-field JPairedStateGenerators.J_pairs` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L53 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L123 [soft] `simp-law-injection` in `simp-declaration stateQGTPhaseReadout_eq_metric_comp_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L132 [soft] `simp-law-injection` in `simp-declaration stateQGTPhaseReadout_eq_metric_comp_modularComplexI` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L165 [soft] `simp-law-injection` in `simp-declaration constantStateModularDatum_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L169 [soft] `simp-law-injection` in `simp-declaration stateModularSeed_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L173 [soft] `simp-law-injection` in `simp-declaration stateTransportGenerator_eq_relativeModularKGenerator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L179 [soft] `simp-law-injection` in `simp-declaration stateRelativeModularGenerator_constant` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L187 [soft] `simp-law-injection` in `simp-declaration stateInducedDynamics_constant` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L195 [soft] `simp-law-injection` in `simp-declaration stateQGTMetricReadout_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L202 [soft] `simp-law-injection` in `simp-declaration stateQGTPhaseReadout_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L212 [soft] `simp-law-injection` in `simp-declaration stateQGTReadout_constant_apply_eq_metricPhase_relativeModularDeriv` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L218 [soft] `skeletal-proof` in `theorem stateQGTReadout_constant_apply_eq_metricPhase_relativeModularDeriv` — proof appears to close via minimal tactic one-liner
  - L268 [soft] `skeletal-proof` in `theorem stateInducedDynamics_eq_gauge_add_source` — proof appears to close via minimal tactic one-liner

