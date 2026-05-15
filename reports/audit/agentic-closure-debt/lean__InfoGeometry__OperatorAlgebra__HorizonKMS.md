# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:15.420690+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/HorizonKMS.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **43**
- Hard: **0**
- Soft: **29**
- Advisory: **14**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/HorizonKMS.lean` | `advisory` | 72 | 0 | 29 | 14 | 43 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/HorizonKMS.lean`
- module: `InfoGeometry.OperatorAlgebra.HorizonKMS`
- status: `advisory`
- debt_score: `72`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L44 [soft] `law-field-locker` in `structure-field KMSReadoutDatum.flow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L46 [soft] `law-field-locker` in `structure-field KMSReadoutDatum.state` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [soft] `law-field-locker` in `structure-field KMSReadoutDatum.beta_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [soft] `law-field-locker` in `structure-field KMSReadoutDatum.flow_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L59 [soft] `law-field-locker` in `structure-field KMSReadoutDatum.flow_add` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L63 [soft] `law-field-locker` in `structure-field KMSReadoutDatum.flow_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [soft] `law-field-locker` in `structure-field KMSReadoutDatum.kms_boundary_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L84 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L133 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L181 [soft] `law-field-locker` in `structure-field HorizonKMSNormalization.surfaceGravity_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L191 [soft] `law-field-locker` in `structure-field HorizonKMSNormalization.beta_eq_two_pi_over_surfaceGravity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L199 [soft] `law-field-locker` in `structure-field HorizonKMSNormalization.temperature_eq_surfaceGravity_over_two_pi` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L207 [soft] `law-field-locker` in `structure-field HorizonKMSNormalization.horizon_modular_calibration` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L221 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L358 [soft] `law-field-locker` in `structure-field GradeTwoMemoryHeatCalibration.observedHeat` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L361 [soft] `law-field-locker` in `structure-field GradeTwoMemoryHeatCalibration.memoryHeat` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L364 [soft] `law-field-locker` in `structure-field GradeTwoMemoryHeatCalibration.observed_heat_eq_gradeTwo_memory_heat` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L387 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L455 [soft] `law-field-locker` in `structure-field HorizonKMSFiveGradeBridge.kms_beta_eq_horizon_beta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L476 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L636 [soft] `law-field-locker` in `structure-field GradeTwoKMSThermalReadout.eventObservable` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L639 [soft] `law-field-locker` in `structure-field GradeTwoKMSThermalReadout.defectScalar` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L642 [soft] `law-field-locker` in `structure-field GradeTwoKMSThermalReadout.memoryScalar` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L645 [soft] `law-field-locker` in `structure-field GradeTwoKMSThermalReadout.memoryScalar_eq_defectScalar` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L654 [soft] `law-field-locker` in `structure-field GradeTwoKMSThermalReadout.kms_reads_hidden_memory` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L672 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L747 [soft] `law-field-locker` in `structure-field GradeTwoMemoryRecoveryData.exteriorData` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L750 [soft] `law-field-locker` in `structure-field GradeTwoMemoryRecoveryData.recovery_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L771 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L833 [soft] `law-field-locker` in `structure-field HorizonKMSThermodynamicMemoryBridge.beta_matches_horizon` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L837 [soft] `law-field-locker` in `structure-field HorizonKMSThermodynamicMemoryBridge.memoryToOperator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L846 [soft] `law-field-locker` in `structure-field HorizonKMSThermodynamicMemoryBridge.hidden_memory_in_commutant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L865 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L893 [advisory] `existential-packaging` in `theorem observer_sees_kms` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L948 [advisory] `existential-packaging` in `def HorizonKMSFiveGradeBridgeOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L994 [advisory] `existential-packaging` in `def GradeTwoMemoryRecoveryOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1010 [advisory] `existential-packaging` in `def HorizonKMSThermodynamicMemoryBridgeOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1053 [soft] `law-field-locker` in `structure-field ExteriorKMSFlowCalibration.modularFlowHorizon` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1056 [soft] `law-field-locker` in `structure-field ExteriorKMSFlowCalibration.modularFlowHorizon_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1060 [soft] `law-field-locker` in `structure-field ExteriorKMSFlowCalibration.modularFlowHorizon_add` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1066 [soft] `law-field-locker` in `structure-field ExteriorKMSFlowCalibration.exterior_kms_flow_eq_modular` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1088 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

