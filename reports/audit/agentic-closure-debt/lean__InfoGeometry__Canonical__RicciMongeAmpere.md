# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:53.265886+00:00`
Root: `lean/InfoGeometry/Canonical/RicciMongeAmpere.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **30**
- Hard: **0**
- Soft: **16**
- Advisory: **14**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RicciMongeAmpere.lean` | `advisory` | 46 | 0 | 16 | 14 | 30 |

## Findings by file

### `lean/InfoGeometry/Canonical/RicciMongeAmpere.lean`
- module: `InfoGeometry.Canonical.RicciMongeAmpere`
- status: `advisory`
- debt_score: `46`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [soft] `law-field-locker` in `structure-field RicciData.symmetric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L38 [advisory] `existential-packaging` in `def IsEinsteinKaehlerAt` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L46 [advisory] `existential-packaging` in `lemma scalarCurvatureOnFrame_eq_einstein_multiple` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L137 [soft] `law-field-locker` in `structure-field StrongRicciFromHessian.symmetric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L138 [soft] `law-field-locker` in `structure-field StrongRicciFromHessian.nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L139 [soft] `law-field-locker` in `structure-field StrongRicciFromHessian.ricci_eq_metric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L144 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L149 [soft] `simp-law-injection` in `simp-declaration ricci_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L174 [advisory] `existential-packaging` in `theorem ricci_component_invariant_at_fixed_point` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L183 [advisory] `local-hypothesis-injection` in `theorem ricci_component_invariant_at_fixed_point` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L185 [advisory] `local-hypothesis-injection` in `theorem ricci_component_invariant_at_fixed_point` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L191 [advisory] `existential-packaging` in `theorem ricci_tensor_invariant_at_fixed_point` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L218 [advisory] `existential-packaging` in `theorem scalarRicci_invariant_at_fixed_point` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L259 [soft] `skeletal-proof` in `lemma normalizedKaehlerRicci_fixedpoint_eq_zero` — proof appears to close via minimal tactic one-liner
  - L270 [advisory] `local-hypothesis-injection` in `lemma normalizedKaehlerRicci_fixedpoint_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L386 [soft] `law-field-locker` in `structure-field SplitVielbein.plus_norm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L387 [soft] `law-field-locker` in `structure-field SplitVielbein.minus_norm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L388 [soft] `law-field-locker` in `structure-field SplitVielbein.orthogonal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L396 [soft] `law-field-locker` in `structure-field SpinConnection.transport` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L397 [soft] `law-field-locker` in `structure-field SpinConnection.preserves_plus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L398 [soft] `law-field-locker` in `structure-field SpinConnection.preserves_minus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L399 [soft] `law-field-locker` in `structure-field SpinConnection.preserves_orthogonal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L539 [advisory] `local-hypothesis-injection` in `lemma vacuum_on_transportedSplit_of_curvature_action_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L541 [advisory] `local-hypothesis-injection` in `lemma vacuum_on_transportedSplit_of_curvature_action_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L588 [soft] `simp-law-injection` in `simp-declaration spinorialScalarCurvature_eq_neg_six_spectralBasepointLogVolume` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L607 [soft] `skeletal-proof` in `theorem normalizedKaehlerRicci_beta_eq_neg_spinorial` — proof appears to close via minimal tactic one-liner
  - L623 [soft] `skeletal-proof` in `theorem spinorialScalarCurvature_eq_zero_of_normalized_fixedpoint` — proof appears to close via minimal tactic one-liner
  - L634 [advisory] `local-hypothesis-injection` in `theorem spinorialScalarCurvature_eq_zero_of_normalized_fixedpoint` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L736 [advisory] `local-hypothesis-injection` in `lemma spectralMongeAmpereDensity_eq_exp_spectralBasepointLogVolume` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

