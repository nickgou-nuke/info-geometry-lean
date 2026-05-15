# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:47.420508+00:00`
Root: `lean/InfoGeometry/Thermo/ModularKLDivergence.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **2**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Thermo/ModularKLDivergence.lean` | `advisory` | 8 | 0 | 2 | 4 | 6 |

## Findings by file

### `lean/InfoGeometry/Thermo/ModularKLDivergence.lean`
- module: `InfoGeometry.Thermo.ModularKLDivergence`
- status: `advisory`
- debt_score: `8`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L51 [advisory] `existential-packaging` in `theorem operatorial_gibbs_variational_principle_frozen_scalar` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L51 [soft] `skeletal-proof` in `theorem operatorial_gibbs_variational_principle_frozen_scalar` — proof appears to close via minimal tactic one-liner
  - L104 [advisory] `existential-packaging` in `theorem relative_modular_hamiltonian_readout_self` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L118 [advisory] `existential-packaging` in `theorem generalizedKL_scale_shape_split` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L118 [soft] `skeletal-proof` in `theorem generalizedKL_scale_shape_split` — proof appears to close via minimal tactic one-liner

