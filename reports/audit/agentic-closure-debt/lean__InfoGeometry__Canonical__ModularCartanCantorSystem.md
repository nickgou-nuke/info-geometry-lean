# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:28.853301+00:00`
Root: `lean/InfoGeometry/Canonical/ModularCartanCantorSystem.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **47**
- Hard: **0**
- Soft: **30**
- Advisory: **17**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ModularCartanCantorSystem.lean` | `advisory` | 77 | 0 | 30 | 17 | 47 |

## Findings by file

### `lean/InfoGeometry/Canonical/ModularCartanCantorSystem.lean`
- module: `InfoGeometry.Canonical.ModularCartanCantorSystem`
- status: `advisory`
- debt_score: `77`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L43 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L45 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L61 [soft] `skeletal-proof` in `theorem modularTwin_modularTwin_of_involutive` — proof appears to close via minimal tactic one-liner
  - L186 [soft] `skeletal-proof` in `theorem cylinderLogIncrement_common_pos_smul` — proof appears to close via minimal tactic one-liner
  - L194 [advisory] `local-hypothesis-injection` in `theorem cylinderLogIncrement_common_pos_smul` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L220 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L265 [soft] `law-field-locker` in `structure-field StandardFormNormalCone.coneVector` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L268 [soft] `law-field-locker` in `structure-field StandardFormNormalCone.coneVector_mem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L271 [soft] `law-field-locker` in `structure-field StandardFormNormalCone.J_involutive` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L274 [soft] `law-field-locker` in `structure-field StandardFormNormalCone.J_fixes_naturalCone` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L277 [soft] `law-field-locker` in `structure-field StandardFormNormalCone.selfdual_cone_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L283 [soft] `law-field-locker` in `structure-field StandardFormNormalCone.outward_normal_cone_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L288 [soft] `law-field-locker` in `structure-field StandardFormNormalCone.inward_normal_cone_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L295 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L295 [soft] `section-law-variable` in `variable S` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L312 [advisory] `bridge-shaped-declaration` in `theorem selfdual_cone_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L339 [advisory] `existential-packaging` in `structure SupportedNaturalConeFaces` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L340 [soft] `law-field-locker` in `structure-field SupportedNaturalConeFaces.standardForm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L342 [soft] `law-field-locker` in `structure-field SupportedNaturalConeFaces.supportProjection` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L345 [soft] `law-field-locker` in `structure-field SupportedNaturalConeFaces.complementProjection` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L348 [soft] `law-field-locker` in `structure-field SupportedNaturalConeFaces.face` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L351 [soft] `law-field-locker` in `structure-field SupportedNaturalConeFaces.faceLocalizer` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L354 [soft] `law-field-locker` in `structure-field SupportedNaturalConeFaces.face_eq_localizer_image` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L359 [soft] `law-field-locker` in `structure-field SupportedNaturalConeFaces.coneVector_mem_supportFace` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L364 [soft] `law-field-locker` in `structure-field SupportedNaturalConeFaces.outward_normal_at_support_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L372 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L372 [soft] `section-law-variable` in `variable F` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L378 [advisory] `bridge-shaped-declaration` in `theorem face_eq_localizer_image_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L378 [advisory] `existential-packaging` in `theorem face_eq_localizer_image_readback` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L385 [advisory] `bridge-shaped-declaration` in `theorem coneVector_mem_supportFace_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L428 [soft] `law-field-locker` in `structure-field RelativeEntropyBarrierSocket.modularScore` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L432 [soft] `law-field-locker` in `structure-field RelativeEntropyBarrierSocket.modular_score_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L438 [soft] `law-field-locker` in `structure-field RelativeEntropyBarrierSocket.finite_split_approximant_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L449 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L449 [soft] `section-law-variable` in `variable B` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L484 [advisory] `bridge-shaped-declaration` in `theorem modular_score_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L490 [advisory] `bridge-shaped-declaration` in `theorem finite_split_approximant_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L514 [soft] `law-field-locker` in `structure-field ModularInformationMetricPullback.stateMap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L516 [soft] `law-field-locker` in `structure-field ModularInformationMetricPullback.stateDerivative` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L519 [soft] `law-field-locker` in `structure-field ModularInformationMetricPullback.modularMetric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L522 [soft] `law-field-locker` in `structure-field ModularInformationMetricPullback.metric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L525 [soft] `law-field-locker` in `structure-field ModularInformationMetricPullback.metric_pullback_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L531 [soft] `law-field-locker` in `structure-field ModularInformationMetricPullback.modular_metric_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L542 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L542 [soft] `section-law-variable` in `variable P` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L555 [advisory] `bridge-shaped-declaration` in `theorem modular_metric_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

