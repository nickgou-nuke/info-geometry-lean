# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:05.965941+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/BoundedTransformSpectralTriple.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **25**
- Hard: **0**
- Soft: **18**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/BoundedTransformSpectralTriple.lean` | `advisory` | 43 | 0 | 18 | 7 | 25 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/BoundedTransformSpectralTriple.lean`
- module: `InfoGeometry.OperatorAlgebra.BoundedTransformSpectralTriple`
- status: `advisory`
- debt_score: `43`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L44 [soft] `law-field-locker` in `structure-field ClosedSelfAdjointSource.apply` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [soft] `law-field-locker` in `structure-field ClosedSelfAdjointSource.includeDomain` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L50 [soft] `law-field-locker` in `structure-field ClosedSelfAdjointSource.denselyDefined_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [soft] `law-field-locker` in `structure-field ClosedSelfAdjointSource.closedGraph_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L60 [soft] `law-field-locker` in `structure-field ClosedSelfAdjointSource.selfAdjoint_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L86 [soft] `law-field-locker` in `structure-field CayleyTransformDatum.unitary_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L91 [soft] `law-field-locker` in `structure-field CayleyTransformDatum.cayley_source_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L99 [soft] `law-field-locker` in `structure-field CayleyTransformDatum.recovery_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L113 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L122 [soft] `skeletal-proof` in `theorem phaseLinear_self` — proof appears to close via minimal tactic one-liner
  - L145 [soft] `law-field-locker` in `structure-field PhaseResolventDatum.denom_right` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L149 [soft] `law-field-locker` in `structure-field PhaseResolventDatum.denom_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L193 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L232 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L252 [soft] `skeletal-proof` in `theorem formula` — proof appears to close via minimal tactic one-liner
  - L285 [soft] `law-field-locker` in `structure-field BoundedTransformDatum.selfAdjoint_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L290 [soft] `law-field-locker` in `structure-field BoundedTransformDatum.bounded_transform_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L295 [soft] `law-field-locker` in `structure-field BoundedTransformDatum.fredholm_or_summability_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L300 [soft] `law-field-locker` in `structure-field BoundedTransformDatum.source_transform_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L314 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L349 [soft] `law-field-locker` in `structure-field UnboundedSpectralBridge.cayley_boundedTransform_compatible_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L388 [soft] `law-field-locker` in `structure-field BoundedTransformSpectralTriple.metric_sensor_compatibility_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L407 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L435 [advisory] `existential-packaging` in `def BoundedTransformSpectralTripleOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

