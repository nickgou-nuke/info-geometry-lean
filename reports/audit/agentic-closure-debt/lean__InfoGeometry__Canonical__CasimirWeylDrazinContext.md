# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:48.923346+00:00`
Root: `lean/InfoGeometry/Canonical/CasimirWeylDrazinContext.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **6**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/CasimirWeylDrazinContext.lean` | `advisory` | 16 | 0 | 6 | 4 | 10 |

## Findings by file

### `lean/InfoGeometry/Canonical/CasimirWeylDrazinContext.lean`
- module: `InfoGeometry.Canonical.CasimirWeylDrazinContext`
- status: `advisory`
- debt_score: `16`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L37 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L52 [soft] `law-field-locker` in `structure-field CasimirWeylDrazinData.observer` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L53 [soft] `law-field-locker` in `structure-field CasimirWeylDrazinData.flow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L56 [soft] `law-field-locker` in `structure-field CasimirWeylDrazinData.lambdaInfo_eq_zetaCasimirResidual` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L122 [soft] `skeletal-proof` in `theorem sourcedGenerator_respects_drazin_cut` — proof appears to close via minimal tactic one-liner
  - L134 [soft] `skeletal-proof` in `theorem sourcedGenerator_bulk_invariant` — proof appears to close via minimal tactic one-liner
  - L147 [soft] `skeletal-proof` in `theorem sourcedGenerator_boundary_excitation` — proof appears to close via minimal tactic one-liner
  - L215 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface

