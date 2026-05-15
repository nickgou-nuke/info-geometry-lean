# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:10.875402+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/CondensateSaturationAudit.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **15**
- Hard: **0**
- Soft: **9**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/CondensateSaturationAudit.lean` | `advisory` | 24 | 0 | 9 | 6 | 15 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/CondensateSaturationAudit.lean`
- module: `InfoGeometry.OperatorAlgebra.CondensateSaturationAudit`
- status: `advisory`
- debt_score: `24`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L30 [soft] `law-field-locker` in `structure-field CondensateCapacityWitness.load` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L32 [soft] `law-field-locker` in `structure-field CondensateCapacityWitness.capacity_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L35 [soft] `law-field-locker` in `structure-field CondensateCapacityWitness.load_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L38 [soft] `law-field-locker` in `structure-field CondensateCapacityWitness.safetyMargin_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L45 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L91 [soft] `law-field-locker` in `structure-field MirrorHealthWitness.reflectionEfficiency` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L92 [soft] `law-field-locker` in `structure-field MirrorHealthWitness.leakage` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L93 [soft] `law-field-locker` in `structure-field MirrorHealthWitness.balanceResidual` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L102 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L154 [soft] `law-field-locker` in `structure-field ModularFlatteningWitness.deltaResidualToIdentity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L160 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L182 [soft] `law-field-locker` in `structure-field RecoveryBacklogWitness.unrecoveredDefectCount` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L188 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L222 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

