# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:36.311459+00:00`
Root: `lean/InfoGeometry/Geometry/ChiralTubuleBoundary.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **25**
- Hard: **0**
- Soft: **19**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Geometry/ChiralTubuleBoundary.lean` | `advisory` | 44 | 0 | 19 | 6 | 25 |

## Findings by file

### `lean/InfoGeometry/Geometry/ChiralTubuleBoundary.lean`
- module: `InfoGeometry.Geometry.ChiralTubuleBoundary`
- status: `advisory`
- debt_score: `44`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [soft] `law-field-locker` in `structure-field BregmanHessianDatum.hessian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L36 [soft] `law-field-locker` in `structure-field BregmanHessianDatum.isInvertibleAt` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L39 [soft] `law-field-locker` in `structure-field BregmanHessianDatum.bregman_hessian_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L63 [soft] `law-field-locker` in `structure-field DualFlatOperatorGeometry.nablaExp` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L64 [soft] `law-field-locker` in `structure-field DualFlatOperatorGeometry.nablaMix` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L65 [soft] `law-field-locker` in `structure-field DualFlatOperatorGeometry.levi_civita_balance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L106 [soft] `law-field-locker` in `structure-field ThermalDriveDatum.temperature` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L111 [soft] `law-field-locker` in `structure-field ThermalDriveDatum.thermal_calibration_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L137 [soft] `law-field-locker` in `structure-field ThermalShearCalibration.shearThreshold_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L140 [soft] `law-field-locker` in `structure-field ThermalShearCalibration.thermal_critical_implies_extreme_shear` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L165 [soft] `law-field-locker` in `structure-field MajoranaWeylResidueDatum.majorana_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L168 [soft] `law-field-locker` in `structure-field MajoranaWeylResidueDatum.weyl_chiral_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L171 [soft] `law-field-locker` in `structure-field MajoranaWeylResidueDatum.lightlike_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L208 [soft] `law-field-locker` in `structure-field ChiralTubuleCrystallization.exponential_connection_trapped_in_R` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L211 [soft] `law-field-locker` in `structure-field ChiralTubuleCrystallization.mixture_connection_trapped_in_L` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L214 [soft] `law-field-locker` in `structure-field ChiralTubuleCrystallization.PT_inversion_boundary_calibration` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L239 [advisory] `existential-packaging` in `structure ChiralTubuleTransitionLaw` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L258 [soft] `law-field-locker` in `structure-field ChiralTubuleTransitionLaw.threshold_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L261 [soft] `law-field-locker` in `structure-field ChiralTubuleTransitionLaw.snap_transition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L283 [advisory] `existential-packaging` in `theorem snap_implies_crystallization` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L324 [soft] `law-field-locker` in `structure-field ThermalTriggeredTubuleLaw.threshold_agrees` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L338 [advisory] `existential-packaging` in `theorem thermal_snap_implies_crystallization` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L382 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L394 [advisory] `existential-packaging` in `def ChiralTubuleBoundaryOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

