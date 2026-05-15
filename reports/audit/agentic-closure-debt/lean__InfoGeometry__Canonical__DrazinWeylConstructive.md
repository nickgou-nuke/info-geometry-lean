# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:05.601244+00:00`
Root: `lean/InfoGeometry/Canonical/DrazinWeylConstructive.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **8**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DrazinWeylConstructive.lean` | `advisory` | 21 | 0 | 8 | 5 | 13 |

## Findings by file

### `lean/InfoGeometry/Canonical/DrazinWeylConstructive.lean`
- module: `InfoGeometry.Canonical.DrazinWeylConstructive`
- status: `advisory`
- debt_score: `21`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L20 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L22 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L35 [soft] `law-field-locker` in `structure-field ConstructiveDrazinWeylData.commutes_spectralEpsilon` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L44 [soft] `law-field-locker` in `structure-field ConstructiveRieszWeylData.riesz` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L45 [soft] `law-field-locker` in `structure-field ConstructiveRieszWeylData.candidate_commutes_spectralEpsilon` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L59 [soft] `law-field-locker` in `structure-field ConstructiveRieszLocalWeylSymmetryData.riesz` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L60 [soft] `law-field-locker` in `structure-field ConstructiveRieszLocalWeylSymmetryData.operator_commutes_spectralEpsilon` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L62 [soft] `law-field-locker` in `structure-field ConstructiveRieszLocalWeylSymmetryData.projector_commutes_spectralEpsilon` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L65 [soft] `law-field-locker` in `structure-field ConstructiveRieszLocalWeylSymmetryData.regular_inverse_unique` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L91 [soft] `skeletal-proof` in `theorem spectralEpsilon_conj_constructiveDrazinCandidate_eq` — proof appears to close via minimal tactic one-liner
  - L215 [advisory] `existential-packaging` in `theorem exists_isDrazinInverse_isWeylCompatible_of_constructiveRieszWeylData` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L230 [advisory] `existential-packaging` in `theorem exists_isDrazinInverse_isWeylCompatible_of_localWeylSymmetry` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

