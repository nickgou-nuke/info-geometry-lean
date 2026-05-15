# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:17.374289+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/KreinIsotropicCone.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **37**
- Hard: **0**
- Soft: **26**
- Advisory: **11**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/KreinIsotropicCone.lean` | `advisory` | 63 | 0 | 26 | 11 | 37 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/KreinIsotropicCone.lean`
- module: `InfoGeometry.OperatorAlgebra.KreinIsotropicCone`
- status: `advisory`
- debt_score: `63`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L28 [soft] `law-field-locker` in `structure-field KreinQuadraticDatum.q` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L30 [soft] `law-field-locker` in `structure-field KreinQuadraticDatum.smul_q` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L34 [soft] `law-field-locker` in `structure-field KreinQuadraticDatum.kreinCertificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L41 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L74 [advisory] `existential-packaging` in `def SameProjectiveRay` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L155 [soft] `law-field-locker` in `structure-field IsotropicAlgebraicBridge.represent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L158 [soft] `law-field-locker` in `structure-field IsotropicAlgebraicBridge.null_maps_to_square_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L164 [soft] `law-field-locker` in `structure-field IsotropicAlgebraicBridge.square_zero_reflects_null` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L174 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L198 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L222 [soft] `law-field-locker` in `structure-field IsotropicDrazinBridge.represent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L228 [soft] `law-field-locker` in `structure-field IsotropicDrazinBridge.null_maps_to_nilpotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L234 [soft] `law-field-locker` in `structure-field IsotropicDrazinBridge.null_supported_by_nil` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L240 [soft] `law-field-locker` in `structure-field IsotropicDrazinBridge.regular_supported_by_core` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L250 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L286 [soft] `law-field-locker` in `structure-field KreinMetricDatum.eta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L287 [soft] `law-field-locker` in `structure-field KreinMetricDatum.eta_self_adjoint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L288 [soft] `law-field-locker` in `structure-field KreinMetricDatum.eta_involutive` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L342 [soft] `law-field-locker` in `structure-field ProjectiveAbsoluteBoundaryDatum.boundary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L345 [soft] `law-field-locker` in `structure-field ProjectiveAbsoluteBoundaryDatum.boundary_iff_isotropic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L349 [soft] `law-field-locker` in `structure-field ProjectiveAbsoluteBoundaryDatum.poincareDistance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L352 [soft] `law-field-locker` in `structure-field ProjectiveAbsoluteBoundaryDatum.metric_lives_on_interior` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L358 [soft] `law-field-locker` in `structure-field ProjectiveAbsoluteBoundaryDatum.boundaryCrossRatio` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L391 [soft] `law-field-locker` in `structure-field MetricIsotropicAlgebraBridge.repVector` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L392 [soft] `law-field-locker` in `structure-field MetricIsotropicAlgebraBridge.IsZeroDivisor` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L393 [soft] `law-field-locker` in `structure-field MetricIsotropicAlgebraBridge.IsNilSupported` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L394 [soft] `law-field-locker` in `structure-field MetricIsotropicAlgebraBridge.isotropic_maps_to_zeroDivisor` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L397 [soft] `law-field-locker` in `structure-field MetricIsotropicAlgebraBridge.zeroDivisor_maps_to_nilSupport` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L444 [soft] `law-field-locker` in `structure-field HasDrazinInverse.commute` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L448 [soft] `law-field-locker` in `structure-field HasDrazinInverse.inverse_identity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L452 [soft] `law-field-locker` in `structure-field HasDrazinInverse.power_identity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L456 [advisory] `existential-packaging` in `def IsDrazinNilpotent` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L482 [advisory] `bridge-shaped-declaration` in `theorem nilpotent_of_isotropic_bridge_drazin` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L564 [advisory] `local-hypothesis-injection` in `theorem nilProjector_idempotent` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L575 [advisory] `local-hypothesis-injection` in `theorem core_mul_nilProjector` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L586 [advisory] `local-hypothesis-injection` in `theorem nil_mul_coreProjector` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

