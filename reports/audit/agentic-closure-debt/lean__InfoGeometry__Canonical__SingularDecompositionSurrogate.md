# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:55.643126+00:00`
Root: `lean/InfoGeometry/Canonical/SingularDecompositionSurrogate.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **0**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SingularDecompositionSurrogate.lean` | `advisory` | 7 | 0 | 0 | 7 | 7 |

## Findings by file

### `lean/InfoGeometry/Canonical/SingularDecompositionSurrogate.lean`
- module: `InfoGeometry.Canonical.SingularDecompositionSurrogate`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L29 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L31 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L207 [advisory] `existential-packaging` in `theorem superHamiltonian_canonical_split_exists` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L224 [advisory] `bridge-shaped-declaration` in `theorem drazin_singular_closure_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L224 [advisory] `existential-packaging` in `theorem drazin_singular_closure_packet` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L296 [advisory] `bridge-shaped-declaration` in `theorem relativeModular_scaleShapeSplit_bridge_of_commute` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

