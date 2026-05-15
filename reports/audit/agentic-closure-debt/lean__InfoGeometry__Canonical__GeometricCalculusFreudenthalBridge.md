# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:10.450997+00:00`
Root: `lean/InfoGeometry/Canonical/GeometricCalculusFreudenthalBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **15**
- Hard: **0**
- Soft: **11**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/GeometricCalculusFreudenthalBridge.lean` | `advisory` | 26 | 0 | 11 | 4 | 15 |

## Findings by file

### `lean/InfoGeometry/Canonical/GeometricCalculusFreudenthalBridge.lean`
- module: `InfoGeometry.Canonical.GeometricCalculusFreudenthalBridge`
- status: `advisory`
- debt_score: `26`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L64 [soft] `law-field-locker` in `structure-field FreudenthalChargeGeometry.I4` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L65 [soft] `law-field-locker` in `structure-field FreudenthalChargeGeometry.entropy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [soft] `law-field-locker` in `structure-field FreudenthalChargeGeometry.rankCollapseLocus_spec` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L70 [soft] `law-field-locker` in `structure-field FreudenthalChargeGeometry.entropy_eq_quartic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L81 [soft] `law-field-locker` in `structure-field FreudenthalBoundaryCharge.charge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L82 [soft] `law-field-locker` in `structure-field FreudenthalBoundaryCharge.landsOnHorizon` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L97 [soft] `law-field-locker` in `structure-field RankCollapseBoundaryCharge.landsOnRankCollapse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L124 [advisory] `local-hypothesis-injection` in `theorem entropy_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L304 [soft] `law-field-locker` in `structure-field OperatorFreudenthalBoundaryFluxBridge.resolvent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L306 [soft] `law-field-locker` in `structure-field OperatorFreudenthalBoundaryFluxBridge.observer` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L309 [soft] `law-field-locker` in `structure-field OperatorFreudenthalBoundaryFluxBridge.horizonOperator_eq_flux` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L327 [soft] `skeletal-proof` in `theorem horizonOperator_eq_projector` — proof appears to close via minimal tactic one-liner
  - L353 [advisory] `existential-packaging` in `def OperatorFreudenthalBoundaryFluxConstructionProblem` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L367 [advisory] `existential-packaging` in `theorem operatorFreudenthalBoundaryFluxBridge_from_witnesses` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

