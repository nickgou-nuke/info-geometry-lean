# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:35.755604+00:00`
Root: `lean/InfoGeometry/Geometry/BilingualAnalyticity.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **47**
- Hard: **0**
- Soft: **35**
- Advisory: **12**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Geometry/BilingualAnalyticity.lean` | `advisory` | 82 | 0 | 35 | 12 | 47 |

## Findings by file

### `lean/InfoGeometry/Geometry/BilingualAnalyticity.lean`
- module: `InfoGeometry.Geometry.BilingualAnalyticity`
- status: `advisory`
- debt_score: `82`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L16 [soft] `law-field-locker` in `structure-field PhaseStructure.K` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L18 [soft] `law-field-locker` in `structure-field PhaseStructure.K_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L27 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L107 [soft] `law-field-locker` in `structure-field CauchyAnalyticAt.deriv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L114 [soft] `law-field-locker` in `structure-field CauchyAnalyticAt.phase_linear_deriv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L133 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L238 [soft] `skeletal-proof` in `theorem comp_deriv` — proof appears to close via minimal tactic one-liner
  - L318 [soft] `law-field-locker` in `structure-field GeometricIntegralBackend.boundaryIntegral` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L322 [soft] `law-field-locker` in `structure-field GeometricIntegralBackend.volumeIntegral` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L326 [soft] `law-field-locker` in `structure-field GeometricIntegralBackend.geometricDerivative` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L333 [soft] `law-field-locker` in `structure-field GeometricIntegralBackend.stokes_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L339 [soft] `law-field-locker` in `structure-field GeometricIntegralBackend.volumeIntegral_zero_of_pointwise_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L357 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L396 [soft] `law-field-locker` in `structure-field HestenesFormCalibration.formOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L415 [soft] `law-field-locker` in `structure-field HestenesAnalyticOn.cauchyForm_represents_F_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L437 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L488 [soft] `simp-law-injection` in `simp-declaration ofCalibration_cauchyForm` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L490 [soft] `skeletal-proof` in `theorem ofCalibration_cauchyForm` — proof appears to close via minimal tactic one-liner
  - L521 [soft] `law-field-locker` in `structure-field CauchyHestenesCompatibility.cauchyFormOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L525 [soft] `law-field-locker` in `structure-field CauchyHestenesCompatibility.cauchyFormOf_represents` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L532 [soft] `law-field-locker` in `structure-field CauchyHestenesCompatibility.cauchyFormOf_represents_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L537 [soft] `law-field-locker` in `structure-field CauchyHestenesCompatibility.obstructionOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L546 [soft] `law-field-locker` in `structure-field CauchyHestenesCompatibility.obstruction_zero_of_phaseLinear` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L552 [soft] `law-field-locker` in `structure-field CauchyHestenesCompatibility.geometricDerivative_eq_obstruction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L570 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L689 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L756 [soft] `law-field-locker` in `structure-field NoncommutativeCauchyFormCalibration.leftAction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L760 [soft] `law-field-locker` in `structure-field NoncommutativeCauchyFormCalibration.rightAction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L764 [soft] `law-field-locker` in `structure-field NoncommutativeCauchyFormCalibration.IsCentralValue` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L768 [soft] `law-field-locker` in `structure-field NoncommutativeCauchyFormCalibration.left_right_compatibility` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L778 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L881 [soft] `law-field-locker` in `structure-field NoncommutativeCauchyKernel.IsAdmissible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L885 [soft] `law-field-locker` in `structure-field NoncommutativeCauchyKernel.diff` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L889 [soft] `law-field-locker` in `structure-field NoncommutativeCauchyKernel.kernel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L893 [soft] `law-field-locker` in `structure-field NoncommutativeCauchyKernel.left_inverse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L899 [soft] `law-field-locker` in `structure-field NoncommutativeCauchyKernel.right_inverse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L909 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L973 [soft] `law-field-locker` in `structure-field CauchyIntegralFormulaDatum.cauchy_formula_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L993 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L1117 [soft] `skeletal-proof` in `theorem inverse_commutes_of_commutes` — proof appears to close via minimal tactic one-liner
  - L1155 [advisory] `local-hypothesis-injection` in `theorem inverse_phaseLinear_of_twoSided_inverse` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1176 [soft] `law-field-locker` in `structure-field SuppliedOperatorResolventKernel.IsAdmissible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1180 [soft] `law-field-locker` in `structure-field SuppliedOperatorResolventKernel.kernel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1184 [soft] `law-field-locker` in `structure-field SuppliedOperatorResolventKernel.left_inverse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1190 [soft] `law-field-locker` in `structure-field SuppliedOperatorResolventKernel.right_inverse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1200 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

