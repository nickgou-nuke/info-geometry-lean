# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:43.887233+00:00`
Root: `lean/InfoGeometry/SuperMetriplectic/OperatorLorentzCurvature.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **31**
- Hard: **0**
- Soft: **28**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/SuperMetriplectic/OperatorLorentzCurvature.lean` | `advisory` | 59 | 0 | 28 | 3 | 31 |

## Findings by file

### `lean/InfoGeometry/SuperMetriplectic/OperatorLorentzCurvature.lean`
- module: `InfoGeometry.SuperMetriplectic.OperatorLorentzCurvature`
- status: `advisory`
- debt_score: `59`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L26 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L28 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L50 [soft] `law-field-locker` in `structure-field OperatorialCliffordFourierGradeSplit.transformed_eq_grade_sum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L74 [soft] `law-field-locker` in `structure-field BisognanoWichmannModularLorentzPacket.modularFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L75 [soft] `law-field-locker` in `structure-field BisognanoWichmannModularLorentzPacket.lorentzBoostFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L76 [soft] `law-field-locker` in `structure-field BisognanoWichmannModularLorentzPacket.modular_eq_lorentz` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L101 [soft] `law-field-locker` in `structure-field DrazinCoreLorentzInvariancePacket.modularFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L102 [soft] `law-field-locker` in `structure-field DrazinCoreLorentzInvariancePacket.generator_kills_core_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L104 [soft] `law-field-locker` in `structure-field DrazinCoreLorentzInvariancePacket.generator_kills_core_right` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L106 [soft] `law-field-locker` in `structure-field DrazinCoreLorentzInvariancePacket.flow_fixes_core_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L108 [soft] `law-field-locker` in `structure-field DrazinCoreLorentzInvariancePacket.flow_fixes_core_right` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L140 [soft] `law-field-locker` in `structure-field ModularLorentzCommutatorCurvaturePacket.modularFlowX` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L141 [soft] `law-field-locker` in `structure-field ModularLorentzCommutatorCurvaturePacket.modularFlowY` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L142 [soft] `law-field-locker` in `structure-field ModularLorentzCommutatorCurvaturePacket.lorentzBoostX` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L143 [soft] `law-field-locker` in `structure-field ModularLorentzCommutatorCurvaturePacket.lorentzBoostY` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L144 [soft] `law-field-locker` in `structure-field ModularLorentzCommutatorCurvaturePacket.curvatureCommutator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L145 [soft] `law-field-locker` in `structure-field ModularLorentzCommutatorCurvaturePacket.riemannReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L146 [soft] `law-field-locker` in `structure-field ModularLorentzCommutatorCurvaturePacket.modularX_eq_lorentzX` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L148 [soft] `law-field-locker` in `structure-field ModularLorentzCommutatorCurvaturePacket.modularY_eq_lorentzY` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L150 [soft] `law-field-locker` in `structure-field ModularLorentzCommutatorCurvaturePacket.curvatureCommutator_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L154 [soft] `law-field-locker` in `structure-field ModularLorentzCommutatorCurvaturePacket.riemannReadout_eq_curvature` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L193 [soft] `law-field-locker` in `structure-field OperatorLorentzCurvatureCapstone.gradeSplit` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L194 [soft] `law-field-locker` in `structure-field OperatorLorentzCurvatureCapstone.boostX` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L195 [soft] `law-field-locker` in `structure-field OperatorLorentzCurvatureCapstone.boostY` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L196 [soft] `law-field-locker` in `structure-field OperatorLorentzCurvatureCapstone.drazinCore` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L197 [soft] `law-field-locker` in `structure-field OperatorLorentzCurvatureCapstone.curvature` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L198 [soft] `law-field-locker` in `structure-field OperatorLorentzCurvatureCapstone.curvature_modularFlowX_matches_boostX` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L200 [soft] `law-field-locker` in `structure-field OperatorLorentzCurvatureCapstone.curvature_modularFlowY_matches_boostY` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L202 [soft] `law-field-locker` in `structure-field OperatorLorentzCurvatureCapstone.curvature_lorentzBoostX_matches_boostX` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L204 [soft] `law-field-locker` in `structure-field OperatorLorentzCurvatureCapstone.curvature_lorentzBoostY_matches_boostY` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

