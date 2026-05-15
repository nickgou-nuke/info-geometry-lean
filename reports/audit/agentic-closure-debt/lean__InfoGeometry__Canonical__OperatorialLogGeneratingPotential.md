# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:39.532071+00:00`
Root: `lean/InfoGeometry/Canonical/OperatorialLogGeneratingPotential.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **18**
- Hard: **0**
- Soft: **17**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/OperatorialLogGeneratingPotential.lean` | `advisory` | 35 | 0 | 17 | 1 | 18 |

## Findings by file

### `lean/InfoGeometry/Canonical/OperatorialLogGeneratingPotential.lean`
- module: `InfoGeometry.Canonical.OperatorialLogGeneratingPotential`
- status: `advisory`
- debt_score: `35`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L53 [soft] `skeletal-proof` in `theorem operatorialPartitionReadout_eq_readout_exp` — proof appears to close via minimal tactic one-liner
  - L60 [soft] `skeletal-proof` in `theorem operatorialLogGeneratingPotential_eq_log_readout_exp` — proof appears to close via minimal tactic one-liner
  - L65 [soft] `simp-law-injection` in `simp-declaration operatorialPartitionReadout_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L68 [soft] `skeletal-proof` in `theorem operatorialPartitionReadout_zero` — proof appears to close via minimal tactic one-liner
  - L72 [soft] `simp-law-injection` in `simp-declaration operatorialLogGeneratingPotential_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L75 [soft] `skeletal-proof` in `theorem operatorialLogGeneratingPotential_zero` — proof appears to close via minimal tactic one-liner
  - L79 [soft] `simp-law-injection` in `simp-declaration operatorialPartitionReadout_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L82 [soft] `skeletal-proof` in `theorem operatorialPartitionReadout_one` — proof appears to close via minimal tactic one-liner
  - L89 [soft] `skeletal-proof` in `theorem hasDerivAt_operatorialPartitionReadout_zero` — proof appears to close via minimal tactic one-liner
  - L100 [soft] `skeletal-proof` in `theorem hasDerivAt_operatorialLogGeneratingPotential_zero` — proof appears to close via minimal tactic one-liner
  - L110 [soft] `skeletal-proof` in `theorem hasDerivAt_operatorialLogGeneratingPotential_zero_of_normalized` — proof appears to close via minimal tactic one-liner
  - L133 [soft] `skeletal-proof` in `theorem modularBetaPartitionReadout_eq_operatorialPartitionReadout_neg` — proof appears to close via minimal tactic one-liner
  - L142 [soft] `skeletal-proof` in `theorem modularBetaLogGeneratingPotential_eq_operatorialLogGeneratingPotential_neg` — proof appears to close via minimal tactic one-liner
  - L149 [soft] `simp-law-injection` in `simp-declaration modularBetaPartitionReadout_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L152 [soft] `skeletal-proof` in `theorem modularBetaPartitionReadout_zero` — proof appears to close via minimal tactic one-liner
  - L156 [soft] `simp-law-injection` in `simp-declaration modularBetaLogGeneratingPotential_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L159 [soft] `skeletal-proof` in `theorem modularBetaLogGeneratingPotential_zero` — proof appears to close via minimal tactic one-liner

