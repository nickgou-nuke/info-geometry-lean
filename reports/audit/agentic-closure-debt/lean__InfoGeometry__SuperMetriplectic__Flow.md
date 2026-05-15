# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:43.134155+00:00`
Root: `lean/InfoGeometry/SuperMetriplectic/Flow.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **15**
- Hard: **0**
- Soft: **14**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/SuperMetriplectic/Flow.lean` | `advisory` | 29 | 0 | 14 | 1 | 15 |

## Findings by file

### `lean/InfoGeometry/SuperMetriplectic/Flow.lean`
- module: `InfoGeometry.SuperMetriplectic.Flow`
- status: `advisory`
- debt_score: `29`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [soft] `law-field-locker` in `structure-field OnsagerMetricData.onsager` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L33 [soft] `law-field-locker` in `structure-field OnsagerMetricData.pairing` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L34 [soft] `law-field-locker` in `structure-field OnsagerMetricData.metric_symmetric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L36 [soft] `law-field-locker` in `structure-field OnsagerMetricData.metric_nonnegative` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L38 [soft] `law-field-locker` in `structure-field OnsagerMetricData.pairing_zero_right` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L72 [soft] `law-field-locker` in `structure-field MetriplecticFlow.dissipativeFlow_eq_onsager_entropy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L74 [soft] `law-field-locker` in `structure-field MetriplecticFlow.totalFlow_eq_reversible_add_dissipative` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L76 [soft] `law-field-locker` in `structure-field MetriplecticFlow.energy_degeneracy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L78 [soft] `law-field-locker` in `structure-field MetriplecticFlow.entropyProduction_eq_quadratic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L81 [soft] `law-field-locker` in `structure-field MetriplecticFlow.reversible_entropy_change_eq_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L159 [soft] `law-field-locker` in `structure-field CoadjointLeafEntropySplit.leafEntropyChange_eq_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L161 [soft] `law-field-locker` in `structure-field CoadjointLeafEntropySplit.transverseEntropyProduction_nonnegative` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L163 [soft] `law-field-locker` in `structure-field CoadjointLeafEntropySplit.totalEntropyChange_eq_leaf_plus_transverse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L210 [soft] `law-field-locker` in `structure-field RelativisticConformalHydroCapstone.gate_LPK_matches_split` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

