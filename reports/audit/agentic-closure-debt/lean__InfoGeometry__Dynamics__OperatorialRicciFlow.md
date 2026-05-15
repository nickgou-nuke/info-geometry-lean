# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:26.361304+00:00`
Root: `lean/InfoGeometry/Dynamics/OperatorialRicciFlow.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **51**
- Hard: **0**
- Soft: **39**
- Advisory: **12**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Dynamics/OperatorialRicciFlow.lean` | `advisory` | 90 | 0 | 39 | 12 | 51 |

## Findings by file

### `lean/InfoGeometry/Dynamics/OperatorialRicciFlow.lean`
- module: `InfoGeometry.Dynamics.OperatorialRicciFlow`
- status: `advisory`
- debt_score: `90`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L51 [soft] `law-field-locker` in `structure-field OperatorialRicciFlow.trajectory` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [soft] `law-field-locker` in `structure-field OperatorialRicciFlow.vectorField` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L59 [soft] `law-field-locker` in `structure-field OperatorialRicciFlow.timeDerivative` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [soft] `law-field-locker` in `structure-field OperatorialRicciFlow.modelOperator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L71 [soft] `law-field-locker` in `structure-field OperatorialRicciFlow.smooth_flow_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L81 [soft] `law-field-locker` in `structure-field OperatorialRicciFlow.perelman_otto_calibration` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L96 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L125 [soft] `law-field-locker` in `structure-field DrazinPerelmanSurgery.ledgerAt` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L128 [soft] `law-field-locker` in `structure-field DrazinPerelmanSurgery.ledger_operator_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L133 [soft] `law-field-locker` in `structure-field DrazinPerelmanSurgery.applyProjector` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L137 [soft] `law-field-locker` in `structure-field DrazinPerelmanSurgery.postSurgeryState` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L141 [soft] `law-field-locker` in `structure-field DrazinPerelmanSurgery.postSurgery_eq_regularCore` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L157 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L208 [soft] `law-field-locker` in `structure-field OperatorialRicciJKOCompatibility.sampleTime` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L212 [soft] `law-field-locker` in `structure-field OperatorialRicciJKOCompatibility.next_eq_sampled_trajectory` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L223 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L260 [soft] `law-field-locker` in `structure-field OperatorialUnifiedHorizonBridge.jordanState` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L263 [soft] `law-field-locker` in `structure-field OperatorialUnifiedHorizonBridge.horizon_iff_jordan_divisor` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L276 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L329 [soft] `law-field-locker` in `structure-field DrazinData.inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L336 [soft] `law-field-locker` in `structure-field DrazinData.commute` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L340 [soft] `law-field-locker` in `structure-field DrazinData.reflexive` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L344 [soft] `law-field-locker` in `structure-field DrazinData.index_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L348 [soft] `law-field-locker` in `structure-field DrazinData.core_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L352 [soft] `law-field-locker` in `structure-field DrazinData.nil_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L362 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L410 [soft] `law-field-locker` in `structure-field OperatorialWFunctional.W` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L413 [soft] `law-field-locker` in `structure-field OperatorialWFunctional.jordan_barrier_component_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L430 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L449 [soft] `law-field-locker` in `structure-field HessianGradientModel.grad` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L452 [soft] `law-field-locker` in `structure-field HessianGradientModel.lin` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L456 [soft] `law-field-locker` in `structure-field HessianGradientModel.drazin` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L484 [soft] `law-field-locker` in `structure-field DrazinSurgeryContinuation.projectToPostChamber` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L488 [soft] `law-field-locker` in `structure-field DrazinSurgeryContinuation.project_drazinCore_mem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L497 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L539 [soft] `law-field-locker` in `structure-field StratifiedOperatorialFlow.smooth_phase` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L544 [soft] `law-field-locker` in `structure-field StratifiedOperatorialFlow.restart` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L548 [soft] `law-field-locker` in `structure-field StratifiedOperatorialFlow.restart_gt` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L552 [soft] `law-field-locker` in `structure-field StratifiedOperatorialFlow.surgery_phase` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L561 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L630 [soft] `law-field-locker` in `structure-field ReductionTriad.analyticReduction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L633 [soft] `law-field-locker` in `structure-field ReductionTriad.algebraicReduction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L640 [soft] `law-field-locker` in `structure-field ReductionTriad.siegelConstantTerm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L644 [soft] `law-field-locker` in `structure-field ReductionTriad.eisensteinLift` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L648 [soft] `law-field-locker` in `structure-field ReductionTriad.heckeBoundary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L652 [soft] `law-field-locker` in `structure-field ReductionTriad.heckeCusp` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L656 [soft] `law-field-locker` in `structure-field ReductionTriad.constantTerm_eisensteinLift_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L713 [advisory] `existential-packaging` in `def OperatorialRicciFlowOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L721 [advisory] `existential-packaging` in `def DrazinPerelmanSurgeryOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L728 [advisory] `existential-packaging` in `def OperatorialUnifiedHorizonBridgeOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

