# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:47.001195+00:00`
Root: `lean/InfoGeometry/Canonical/BulkBoundaryZeroModeOwner.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **1**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/BulkBoundaryZeroModeOwner.lean` | `advisory` | 6 | 0 | 1 | 4 | 5 |

## Findings by file

### `lean/InfoGeometry/Canonical/BulkBoundaryZeroModeOwner.lean`
- module: `InfoGeometry.Canonical.BulkBoundaryZeroModeOwner`
- status: `advisory`
- debt_score: `6`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L36 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L46 [soft] `law-field-locker` in `structure-field DimensionAgnosticBoundaryZeroModeOwner.boundaryWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L71 [advisory] `existential-packaging` in `theorem owner_exists_zeroMode` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L137 [advisory] `existential-packaging` in `theorem exists_zeroMode_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

