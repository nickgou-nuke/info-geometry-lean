# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:31.588170+00:00`
Root: `lean/InfoGeometry/Canonical/ModularTwoStateCorrelation.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **26**
- Hard: **0**
- Soft: **23**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ModularTwoStateCorrelation.lean` | `advisory` | 49 | 0 | 23 | 3 | 26 |

## Findings by file

### `lean/InfoGeometry/Canonical/ModularTwoStateCorrelation.lean`
- module: `InfoGeometry.Canonical.ModularTwoStateCorrelation`
- status: `advisory`
- debt_score: `49`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L37 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L109 [soft] `simp-law-injection` in `simp-declaration twoStateObservableCorrelation_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L117 [soft] `simp-law-injection` in `simp-declaration twoStateChannelCorrelation_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L130 [soft] `skeletal-proof` in `theorem twoStateObservableCorrelation_swap` — proof appears to close via minimal tactic one-liner
  - L141 [soft] `skeletal-proof` in `theorem twoStateChannelCorrelation_swap` — proof appears to close via minimal tactic one-liner
  - L150 [soft] `skeletal-proof` in `theorem twoStateChannelCorrelation_self_eq_channelCorrelationAtState` — proof appears to close via minimal tactic one-liner
  - L159 [soft] `skeletal-proof` in `theorem comparisonGeneratorMetric_eq_twoStateChannelCorrelation_self` — proof appears to close via minimal tactic one-liner
  - L169 [soft] `skeletal-proof` in `theorem channelCorrelationGap_eq_comparisonGeneratorMetric_sub_reference` — proof appears to close via minimal tactic one-liner
  - L205 [soft] `simp-law-injection` in `simp-declaration stateTransportedOperator_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L208 [soft] `skeletal-proof` in `theorem stateTransportedOperator_zero` — proof appears to close via minimal tactic one-liner
  - L212 [soft] `simp-law-injection` in `simp-declaration comparisonTransportedObservable_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L215 [soft] `skeletal-proof` in `theorem comparisonTransportedObservable_zero` — proof appears to close via minimal tactic one-liner
  - L220 [soft] `simp-law-injection` in `simp-declaration stateTransportCorrelation_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L223 [soft] `skeletal-proof` in `theorem stateTransportCorrelation_zero` — proof appears to close via minimal tactic one-liner
  - L229 [soft] `simp-law-injection` in `simp-declaration stateTransportPhaseShiftedChannelCorrelation_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L232 [soft] `skeletal-proof` in `theorem stateTransportPhaseShiftedChannelCorrelation_zero` — proof appears to close via minimal tactic one-liner
  - L240 [soft] `simp-law-injection` in `simp-declaration comparisonTransportCorrelation_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L243 [soft] `skeletal-proof` in `theorem comparisonTransportCorrelation_zero` — proof appears to close via minimal tactic one-liner
  - L253 [soft] `skeletal-proof` in `theorem comparisonTransportCorrelation_eq_stateTransportCorrelation` — proof appears to close via minimal tactic one-liner
  - L263 [soft] `skeletal-proof` in `theorem comparisonTransportPhaseShiftedChannelCorrelation_eq_stateTransportPhaseShiftedChannelCorrelation` — proof appears to close via minimal tactic one-liner
  - L271 [soft] `simp-law-injection` in `simp-declaration comparisonTransportPhaseShiftedChannelCorrelation_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L274 [soft] `skeletal-proof` in `theorem comparisonTransportPhaseShiftedChannelCorrelation_zero` — proof appears to close via minimal tactic one-liner
  - L290 [soft] `skeletal-proof` in `theorem hasDerivAt_stateTransportPhaseShiftedChannelCorrelation_at_zero` — proof appears to close via minimal tactic one-liner
  - L364 [soft] `skeletal-proof` in `theorem deriv_comparisonTransportPhaseShiftedChannelCorrelation_at_zero_eq_comparisonMetricReadout` — proof appears to close via minimal tactic one-liner

