# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:05.599893+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/AnomalousFlowStabilization.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **7**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/AnomalousFlowStabilization.lean` | `advisory` | 18 | 0 | 7 | 4 | 11 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/AnomalousFlowStabilization.lean`
- module: `InfoGeometry.OperatorAlgebra.AnomalousFlowStabilization`
- status: `advisory`
- debt_score: `18`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L16 [advisory] `existential-packaging` in `structure AnomalousFlowStabilizationWitness` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L29 [soft] `law-field-locker` in `structure-field AnomalousFlowStabilizationWitness.flow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L31 [soft] `law-field-locker` in `structure-field AnomalousFlowStabilizationWitness.anomalyReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L34 [soft] `law-field-locker` in `structure-field AnomalousFlowStabilizationWitness.topologicalCharge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L37 [soft] `law-field-locker` in `structure-field AnomalousFlowStabilizationWitness.charge_invariant_under_flow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L42 [soft] `law-field-locker` in `structure-field AnomalousFlowStabilizationWitness.flat_vacuum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L45 [soft] `law-field-locker` in `structure-field AnomalousFlowStabilizationWitness.nonflat_stable` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L48 [soft] `law-field-locker` in `structure-field AnomalousFlowStabilizationWitness.anomaly_forces_stable_nonflat` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L62 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L70 [advisory] `existential-packaging` in `theorem stable_nonflat_of_anomaly_and_charge` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

