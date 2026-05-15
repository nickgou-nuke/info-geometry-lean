# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:28.978354+00:00`
Root: `lean/InfoGeometry/Canonical/ModularHamiltonianDoubledBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **5**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ModularHamiltonianDoubledBridge.lean` | `advisory` | 13 | 0 | 5 | 3 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/ModularHamiltonianDoubledBridge.lean`
- module: `InfoGeometry.Canonical.ModularHamiltonianDoubledBridge`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L33 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L35 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L59 [soft] `skeletal-proof` in `theorem modularHamiltonian_eq_doubledExpr` — proof appears to close via minimal tactic one-liner
  - L91 [soft] `skeletal-proof` in `theorem canonicalTomitaLogData_Delta_eq_exp_deltaLog` — proof appears to close via minimal tactic one-liner
  - L115 [soft] `skeletal-proof` in `theorem canonicalTomita_deltaLog_eq_neg_superHamiltonian_comp_phaseAxisK` — proof appears to close via minimal tactic one-liner
  - L145 [soft] `skeletal-proof` in `theorem canonicalTomita_generator_eq_deltaLog_comp_modular_j_comp_spectral_epsilon` — proof appears to close via minimal tactic one-liner
  - L161 [soft] `skeletal-proof` in `theorem canonicalTomita_flow_eq_exp_time_generator` — proof appears to close via minimal tactic one-liner

