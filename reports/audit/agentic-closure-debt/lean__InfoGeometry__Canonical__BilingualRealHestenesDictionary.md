# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:42.769256+00:00`
Root: `lean/InfoGeometry/Canonical/BilingualRealHestenesDictionary.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **0**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/BilingualRealHestenesDictionary.lean` | `advisory` | 8 | 0 | 0 | 8 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/BilingualRealHestenesDictionary.lean`
- module: `InfoGeometry.Canonical.BilingualRealHestenesDictionary`
- status: `advisory`
- debt_score: `8`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L25 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L27 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L44 [advisory] `bridge-shaped-declaration` in `theorem modularComplexI_readback_complex_i` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L74 [advisory] `bridge-shaped-declaration` in `theorem complexLinear_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L83 [advisory] `bridge-shaped-declaration` in `theorem complexAntilinear_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L127 [advisory] `bridge-shaped-declaration` in `theorem hestenesPseudoscalar_readback_spectralEpsilon` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L133 [advisory] `bridge-shaped-declaration` in `theorem hestenesPseudoscalar_readback_sq` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

