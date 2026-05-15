# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:57.046311+00:00`
Root: `lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **82**
- Hard: **0**
- Soft: **57**
- Advisory: **25**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean` | `advisory` | 139 | 0 | 57 | 25 | 82 |

## Findings by file

### `lean/InfoGeometry/Canonical/CoordinatelessSouriauKMSBridge.lean`
- module: `InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge`
- status: `advisory`
- debt_score: `139`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L46 [soft] `law-field-locker` in `structure-field AlgebraicState.functional` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [soft] `law-field-locker` in `structure-field AlgebraicState.positive` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L48 [soft] `law-field-locker` in `structure-field AlgebraicState.normalized` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L75 [soft] `law-field-locker` in `structure-field CyclicAlgebraicState.state` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L76 [soft] `law-field-locker` in `structure-field CyclicAlgebraicState.cyclic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L79 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L107 [soft] `law-field-locker` in `structure-field KMSState.state` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L108 [soft] `law-field-locker` in `structure-field KMSState.kms_identity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L113 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L113 [soft] `section-law-variable` in `variable K` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L130 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L164 [soft] `law-field-locker` in `structure-field OperatorSouriauMoment.momentOperator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L170 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L170 [soft] `section-law-variable` in `variable J` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L178 [soft] `skeletal-proof` in `theorem thermalGenerator_eq_moment_geometricTemperature` — proof appears to close via minimal tactic one-liner
  - L192 [soft] `law-field-locker` in `structure-field QuantumFisherSLDMetric.sld` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L193 [soft] `law-field-locker` in `structure-field QuantumFisherSLDMetric.metric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L194 [soft] `law-field-locker` in `structure-field QuantumFisherSLDMetric.metric_eq_sld_readout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L196 [soft] `law-field-locker` in `structure-field QuantumFisherSLDMetric.symmetric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L201 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L201 [soft] `section-law-variable` in `variable Q` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L220 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L255 [soft] `law-field-locker` in `structure-field WeylAlgebraGauge.state_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L260 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L260 [soft] `section-law-variable` in `variable W` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L293 [soft] `law-field-locker` in `structure-field ModularTimeKMSContext.sigma` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L295 [soft] `law-field-locker` in `structure-field ModularTimeKMSContext.kms` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L298 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L298 [soft] `section-law-variable` in `variable M` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L323 [soft] `law-field-locker` in `structure-field CyclicModularTimeKMSContext.state` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L327 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L327 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L346 [soft] `skeletal-proof` in `theorem kms_eval_mul_modular_eq_eval_flip` — proof appears to close via minimal tactic one-liner
  - L353 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L372 [soft] `law-field-locker` in `structure-field CoordinateEmergence.readout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L373 [soft] `law-field-locker` in `structure-field CoordinateEmergence.emergentObservable` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L374 [soft] `law-field-locker` in `structure-field CoordinateEmergence.readout_emergent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L379 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L379 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L399 [soft] `law-field-locker` in `structure-field CoordinatelessSouriauFisherContext.state` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L400 [soft] `law-field-locker` in `structure-field CoordinatelessSouriauFisherContext.sigma` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L402 [soft] `law-field-locker` in `structure-field CoordinatelessSouriauFisherContext.kms` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L403 [soft] `law-field-locker` in `structure-field CoordinatelessSouriauFisherContext.kms_state_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L404 [soft] `law-field-locker` in `structure-field CoordinatelessSouriauFisherContext.souriauMoment` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L405 [soft] `law-field-locker` in `structure-field CoordinatelessSouriauFisherContext.fisherMetric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L406 [soft] `law-field-locker` in `structure-field CoordinatelessSouriauFisherContext.weylGauge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L411 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L411 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L472 [soft] `law-field-locker` in `structure-field MinimalCyclicCoordinatelessSouriauContext.state` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L474 [soft] `law-field-locker` in `structure-field MinimalCyclicCoordinatelessSouriauContext.souriauMoment` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L475 [soft] `law-field-locker` in `structure-field MinimalCyclicCoordinatelessSouriauContext.sld` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L480 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L480 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L507 [soft] `skeletal-proof` in `theorem kms_identity` — proof appears to close via minimal tactic one-liner
  - L544 [advisory] `bridge-shaped-declaration` in `theorem coordinateless_constructive_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L570 [soft] `law-field-locker` in `structure-field ObservableMinimalCyclicCoordinatelessSouriauContext.state` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L572 [soft] `law-field-locker` in `structure-field ObservableMinimalCyclicCoordinatelessSouriauContext.souriauMoment` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L577 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L577 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L597 [soft] `skeletal-proof` in `theorem fisherMetric_sld_eq_id` — proof appears to close via minimal tactic one-liner
  - L609 [soft] `skeletal-proof` in `theorem kms_identity` — proof appears to close via minimal tactic one-liner
  - L634 [advisory] `bridge-shaped-declaration` in `theorem coordinateless_constructive_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L658 [soft] `law-field-locker` in `structure-field ObservableCyclicCoordinatelessSouriauFisherContext.state` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L660 [soft] `law-field-locker` in `structure-field ObservableCyclicCoordinatelessSouriauFisherContext.souriauMoment` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L665 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L665 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L685 [soft] `skeletal-proof` in `theorem fisherMetric_sld_eq_id` — proof appears to close via minimal tactic one-liner
  - L697 [soft] `skeletal-proof` in `theorem kms_identity` — proof appears to close via minimal tactic one-liner
  - L722 [advisory] `bridge-shaped-declaration` in `theorem coordinateless_constructive_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L750 [soft] `law-field-locker` in `structure-field CyclicCoordinatelessSouriauFisherContext.state` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L752 [soft] `law-field-locker` in `structure-field CyclicCoordinatelessSouriauFisherContext.souriauMoment` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L753 [soft] `law-field-locker` in `structure-field CyclicCoordinatelessSouriauFisherContext.fisherMetric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L754 [soft] `law-field-locker` in `structure-field CyclicCoordinatelessSouriauFisherContext.weylGauge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L759 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L759 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L776 [soft] `skeletal-proof` in `theorem kms_identity` — proof appears to close via minimal tactic one-liner
  - L813 [advisory] `bridge-shaped-declaration` in `theorem coordinateless_constructive_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L833 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L909 [advisory] `bridge-shaped-declaration` in `theorem coordinateless_constructive_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

