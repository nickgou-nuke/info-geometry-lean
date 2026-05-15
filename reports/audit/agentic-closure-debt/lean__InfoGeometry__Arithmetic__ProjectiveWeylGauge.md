# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:34.414349+00:00`
Root: `lean/InfoGeometry/Arithmetic/ProjectiveWeylGauge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **25**
- Hard: **0**
- Soft: **20**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Arithmetic/ProjectiveWeylGauge.lean` | `advisory` | 45 | 0 | 20 | 5 | 25 |

## Findings by file

### `lean/InfoGeometry/Arithmetic/ProjectiveWeylGauge.lean`
- module: `InfoGeometry.Arithmetic.ProjectiveWeylGauge`
- status: `advisory`
- debt_score: `45`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L38 [soft] `skeletal-proof` in `theorem projectiveWeylThermalMass_eq` — proof appears to close via minimal tactic one-liner
  - L45 [soft] `skeletal-proof` in `theorem projectiveArithmeticShape_eq` — proof appears to close via minimal tactic one-liner
  - L52 [soft] `skeletal-proof` in `theorem projectiveArithmeticShape_scale_counts` — proof appears to close via minimal tactic one-liner
  - L69 [soft] `law-field-locker` in `structure-field ScaleInvariantReadout.readout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L71 [soft] `law-field-locker` in `structure-field ScaleInvariantReadout.scale_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L80 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L100 [soft] `law-field-locker` in `structure-field PairScaleInvariantReadout.readout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L102 [soft] `law-field-locker` in `structure-field PairScaleInvariantReadout.scale_invariant_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L109 [soft] `law-field-locker` in `structure-field PairScaleInvariantReadout.scale_invariant_right` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L118 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L207 [soft] `law-field-locker` in `structure-field ProjectiveWeylGaugeDecomposition.totalKL_eq_finiteKL` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L212 [soft] `law-field-locker` in `structure-field ProjectiveWeylGaugeDecomposition.shapeCore_eq_shapeKL` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L216 [soft] `law-field-locker` in `structure-field ProjectiveWeylGaugeDecomposition.scalarCore_eq_scalarKL` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L220 [soft] `law-field-locker` in `structure-field ProjectiveWeylGaugeDecomposition.totalKL_eq_weylScale_mul_shapeCore` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L233 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L275 [soft] `law-field-locker` in `structure-field ProjectiveWeylGaugeCalibration.stateOfProfiles` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L278 [soft] `law-field-locker` in `structure-field ProjectiveWeylGaugeCalibration.totalReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L281 [soft] `law-field-locker` in `structure-field ProjectiveWeylGaugeCalibration.weylScaleReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L284 [soft] `law-field-locker` in `structure-field ProjectiveWeylGaugeCalibration.shapeCoreReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L287 [soft] `law-field-locker` in `structure-field ProjectiveWeylGaugeCalibration.decompositionOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L292 [soft] `law-field-locker` in `structure-field ProjectiveWeylGaugeCalibration.total_eq_decomposition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L298 [soft] `law-field-locker` in `structure-field ProjectiveWeylGaugeCalibration.scale_eq_decomposition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L304 [soft] `law-field-locker` in `structure-field ProjectiveWeylGaugeCalibration.shape_eq_decomposition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L314 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

