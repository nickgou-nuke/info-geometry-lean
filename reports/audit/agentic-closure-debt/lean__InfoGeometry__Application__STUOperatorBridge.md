# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:30.720751+00:00`
Root: `lean/InfoGeometry/Application/STUOperatorBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **43**
- Hard: **0**
- Soft: **36**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Application/STUOperatorBridge.lean` | `advisory` | 79 | 0 | 36 | 7 | 43 |

## Findings by file

### `lean/InfoGeometry/Application/STUOperatorBridge.lean`
- module: `InfoGeometry.Application.STUOperatorBridge`
- status: `advisory`
- debt_score: `79`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L23 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L25 [advisory] `existential-packaging` in `structure DrazinWitness` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L37 [soft] `law-field-locker` in `structure-field DrazinWitness.drazin_outer` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L39 [soft] `law-field-locker` in `structure-field DrazinWitness.commute` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L41 [soft] `law-field-locker` in `structure-field DrazinWitness.drazin_power` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L62 [soft] `skeletal-proof` in `theorem drazinCore_add_nil` — proof appears to close via minimal tactic one-liner
  - L85 [soft] `skeletal-proof` in `theorem drazinNilProjector_idempotent` — proof appears to close via minimal tactic one-liner
  - L91 [advisory] `local-hypothesis-injection` in `theorem drazinNilProjector_idempotent` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L106 [soft] `skeletal-proof` in `theorem drazinCore_mul_nil` — proof appears to close via minimal tactic one-liner
  - L111 [advisory] `local-hypothesis-injection` in `theorem drazinCore_mul_nil` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L121 [soft] `skeletal-proof` in `theorem drazinNil_mul_core` — proof appears to close via minimal tactic one-liner
  - L126 [advisory] `local-hypothesis-injection` in `theorem drazinNil_mul_core` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L149 [soft] `law-field-locker` in `structure-field OperatorQuarticInvariant.quartic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L150 [soft] `law-field-locker` in `structure-field OperatorQuarticInvariant.conj_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L191 [soft] `law-field-locker` in `structure-field OperatorFisherMetricWitness.metric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L193 [soft] `law-field-locker` in `structure-field OperatorFisherMetricWitness.inverseMetric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L196 [soft] `law-field-locker` in `structure-field OperatorFisherMetricWitness.dPotential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L199 [soft] `law-field-locker` in `structure-field OperatorFisherMetricWitness.gradient` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L202 [soft] `law-field-locker` in `structure-field OperatorFisherMetricWitness.gradient_spec` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L219 [soft] `law-field-locker` in `structure-field OperatorGradientFlow.vectorField` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L222 [soft] `law-field-locker` in `structure-field OperatorGradientFlow.vectorField_eq_negative_gradient` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L227 [soft] `law-field-locker` in `structure-field OperatorGradientFlow.flow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L271 [soft] `law-field-locker` in `structure-field OperatorSurgeryPacket.coreState` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L275 [soft] `law-field-locker` in `structure-field OperatorSurgeryPacket.radicalState` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L289 [soft] `law-field-locker` in `structure-field BlackHoleQubitOperatorDictionary.invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L291 [soft] `law-field-locker` in `structure-field BlackHoleQubitOperatorDictionary.GHZOperator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L294 [soft] `law-field-locker` in `structure-field BlackHoleQubitOperatorDictionary.BoundaryOperator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L297 [soft] `law-field-locker` in `structure-field BlackHoleQubitOperatorDictionary.ghz_iff_regular` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L301 [soft] `law-field-locker` in `structure-field BlackHoleQubitOperatorDictionary.boundary_iff_quartic_boundary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L305 [soft] `law-field-locker` in `structure-field BlackHoleQubitOperatorDictionary.entropy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L308 [soft] `law-field-locker` in `structure-field BlackHoleQubitOperatorDictionary.entropy_eq_invariant_readout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L312 [advisory] `existential-packaging` in `structure DecoherenceAsDrazinSurgery` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L321 [soft] `law-field-locker` in `structure-field DecoherenceAsDrazinSurgery.decoherenceFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L323 [soft] `law-field-locker` in `structure-field DecoherenceAsDrazinSurgery.detector` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L326 [soft] `law-field-locker` in `structure-field DecoherenceAsDrazinSurgery.drazinInverseAtBoundary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L329 [soft] `law-field-locker` in `structure-field DecoherenceAsDrazinSurgery.hits_boundary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L335 [soft] `law-field-locker` in `structure-field DecoherenceAsDrazinSurgery.surgery_at_boundary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L342 [soft] `law-field-locker` in `structure-field DecoherenceAsDrazinSurgery.post_surgery_state` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L346 [soft] `law-field-locker` in `structure-field DecoherenceAsDrazinSurgery.EndH` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L364 [soft] `law-field-locker` in `structure-field OperatorCoordinateChart.toCoord` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L366 [soft] `law-field-locker` in `structure-field OperatorCoordinateChart.coordInvariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L369 [soft] `law-field-locker` in `structure-field OperatorCoordinateChart.invariant_eq_coordInvariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

