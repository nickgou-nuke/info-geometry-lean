# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:34.219557+00:00`
Root: `lean/InfoGeometry/Quantum/Fock.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **10**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Quantum/Fock.lean` | `advisory` | 21 | 0 | 10 | 1 | 11 |

## Findings by file

### `lean/InfoGeometry/Quantum/Fock.lean`
- module: `InfoGeometry.Quantum.Fock`
- status: `advisory`
- debt_score: `21`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [soft] `skeletal-proof` in `theorem creation_eq_plus_projector` — proof appears to close via minimal tactic one-liner
  - L36 [soft] `skeletal-proof` in `theorem annihilation_eq_minus_projector` — proof appears to close via minimal tactic one-liner
  - L65 [soft] `skeletal-proof` in `theorem commutator_I_J` — proof appears to close via minimal tactic one-liner
  - L71 [soft] `skeletal-proof` in `theorem commutator_J_epsilon_eq_two_I` — proof appears to close via minimal tactic one-liner
  - L77 [soft] `skeletal-proof` in `theorem annihilation_kills_vacuum_vector` — proof appears to close via minimal tactic one-liner
  - L90 [soft] `skeletal-proof` in `theorem data_model_decomposition` — proof appears to close via minimal tactic one-liner
  - L101 [soft] `simp-law-injection` in `simp-declaration bayesianAddData_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L110 [soft] `skeletal-proof` in `theorem bayesian_update_preserves_data_independence` — proof appears to close via minimal tactic one-liner
  - L120 [soft] `skeletal-proof` in `theorem inducedSymplecticForm_eq_complex_pairing` — proof appears to close via minimal tactic one-liner
  - L125 [soft] `skeletal-proof` in `theorem vacuum_is_zero_ray` — proof appears to close via minimal tactic one-liner

