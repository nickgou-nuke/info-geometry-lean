# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:13.807941+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ExceptionalVirasoroBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **26**
- Hard: **0**
- Soft: **20**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ExceptionalVirasoroBridge.lean` | `advisory` | 46 | 0 | 20 | 6 | 26 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ExceptionalVirasoroBridge.lean`
- module: `InfoGeometry.OperatorAlgebra.ExceptionalVirasoroBridge`
- status: `advisory`
- debt_score: `46`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L66 [soft] `law-field-locker` in `structure-field HiddenMemoryAffineCurrentCalibration.memoryToAffine` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L70 [soft] `law-field-locker` in `structure-field HiddenMemoryAffineCurrentCalibration.modeOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L74 [soft] `law-field-locker` in `structure-field HiddenMemoryAffineCurrentCalibration.finiteChargeOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L78 [soft] `law-field-locker` in `structure-field HiddenMemoryAffineCurrentCalibration.hidden_memory_is_current_mode` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L84 [soft] `law-field-locker` in `structure-field HiddenMemoryAffineCurrentCalibration.finite_exceptional_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L89 [soft] `law-field-locker` in `structure-field HiddenMemoryAffineCurrentCalibration.affine_exceptional_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L109 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L162 [soft] `law-field-locker` in `structure-field HiddenMemoryVirasoroReadout.stressScalar` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L166 [soft] `law-field-locker` in `structure-field HiddenMemoryVirasoroReadout.memoryScalar` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L170 [soft] `law-field-locker` in `structure-field HiddenMemoryVirasoroReadout.defectScalar` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L174 [soft] `law-field-locker` in `structure-field HiddenMemoryVirasoroReadout.memory_scalar_eq_stress_scalar` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L180 [soft] `law-field-locker` in `structure-field HiddenMemoryVirasoroReadout.defect_scalar_eq_memory_scalar` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L186 [soft] `law-field-locker` in `structure-field HiddenMemoryVirasoroReadout.central_anomaly_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L207 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L309 [soft] `law-field-locker` in `structure-field HorizonExceptionalVirasoroBridge.kms_flux_eq_virasoro_stress_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L314 [soft] `law-field-locker` in `structure-field HorizonExceptionalVirasoroBridge.central_charge_is_grade_two_memory_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L333 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L439 [soft] `law-field-locker` in `structure-field HiddenMemoryCentralChargeReadout.centralReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L443 [soft] `law-field-locker` in `structure-field HiddenMemoryCentralChargeReadout.hiddenMemoryChargeReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L447 [soft] `law-field-locker` in `structure-field HiddenMemoryCentralChargeReadout.central_equals_hidden_memory` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L455 [soft] `law-field-locker` in `structure-field HiddenMemoryCentralChargeReadout.boundary_stress_interpretation_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L482 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L539 [soft] `law-field-locker` in `structure-field HorizonKMSVirasoroChargeCompatibility.kmsChargeReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L543 [soft] `law-field-locker` in `structure-field HorizonKMSVirasoroChargeCompatibility.kms_defect_eq_virasoro_central` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L572 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

