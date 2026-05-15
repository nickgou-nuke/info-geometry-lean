# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:22.855656+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/SpinUnruhCalibration.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **19**
- Hard: **0**
- Soft: **12**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/SpinUnruhCalibration.lean` | `advisory` | 31 | 0 | 12 | 7 | 19 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/SpinUnruhCalibration.lean`
- module: `InfoGeometry.OperatorAlgebra.SpinUnruhCalibration`
- status: `advisory`
- debt_score: `31`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L30 [soft] `law-field-locker` in `structure-field SpinModularCompatibility.modularFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L32 [soft] `law-field-locker` in `structure-field SpinModularCompatibility.physicalBoostFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L38 [soft] `law-field-locker` in `structure-field SpinModularCompatibility.acceleration_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L41 [soft] `law-field-locker` in `structure-field SpinModularCompatibility.modular_physical_calibration_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L53 [soft] `law-field-locker` in `structure-field SpinModularCompatibility.spin_connection_generates_boost_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L64 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L107 [soft] `law-field-locker` in `structure-field UnruhTemperatureCalibration.temperature_eq_unruh` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L115 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L160 [soft] `law-field-locker` in `structure-field ModularAccelerationCalibration.betaModular_eq_two_pi` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L167 [soft] `law-field-locker` in `structure-field ModularAccelerationCalibration.betaPhysical_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L174 [soft] `law-field-locker` in `structure-field ModularAccelerationCalibration.temperature_eq_inv_beta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L180 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L230 [soft] `law-field-locker` in `structure-field ModularBoostTemperatureCalibration.acceleration_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L234 [soft] `law-field-locker` in `structure-field ModularBoostTemperatureCalibration.modular_flow_is_boost_flow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L241 [soft] `law-field-locker` in `structure-field ModularBoostTemperatureCalibration.beta_eq_unruhBeta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L251 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L269 [advisory] `existential-packaging` in `def ModularUnruhCalibrationOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L276 [advisory] `existential-packaging` in `def SpinUnruhCalibrationOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

