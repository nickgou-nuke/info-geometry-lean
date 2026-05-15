# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:54.282121+00:00`
Root: `lean/InfoGeometry/Canonical/SUSYBayes.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **4**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SUSYBayes.lean` | `advisory` | 13 | 0 | 4 | 5 | 9 |

## Findings by file

### `lean/InfoGeometry/Canonical/SUSYBayes.lean`
- module: `InfoGeometry.Canonical.SUSYBayes`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L60 [soft] `skeletal-proof` in `theorem super_even_even_eq_commutator` — proof appears to close via minimal tactic one-liner
  - L68 [soft] `skeletal-proof` in `theorem super_odd_odd_eq_anticommutator` — proof appears to close via minimal tactic one-liner
  - L82 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L83 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L84 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L85 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L86 [soft] `skeletal-proof` in `theorem einstein_inducedChemicalPotential_eq_transportedResidual` — proof appears to close via minimal tactic one-liner
  - L94 [soft] `skeletal-proof` in `theorem grandCanonical_eq_hamiltonian_of_vacuumTransported` — proof appears to close via minimal tactic one-liner

