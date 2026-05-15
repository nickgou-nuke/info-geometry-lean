# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:50.170846+00:00`
Root: `lean/InfoGeometry/Canonical/RelativeModularBerezinianBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **26**
- Hard: **0**
- Soft: **16**
- Advisory: **10**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RelativeModularBerezinianBridge.lean` | `advisory` | 42 | 0 | 16 | 10 | 26 |

## Findings by file

### `lean/InfoGeometry/Canonical/RelativeModularBerezinianBridge.lean`
- module: `InfoGeometry.Canonical.RelativeModularBerezinianBridge`
- status: `advisory`
- debt_score: `42`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L36 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L54 [soft] `skeletal-proof` in `theorem relativeModularSheetEquiv_toLinearMap` — proof appears to close via minimal tactic one-liner
  - L110 [advisory] `existential-packaging` in `theorem neg_log_relativeModularRestrictedSheetEquiv_restrictedVolumeScale_eq_supervolumePotential` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L125 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L157 [soft] `skeletal-proof` in `theorem relativeModularSupervolumeKreinQuadraticPotential_zero` — proof appears to close via minimal tactic one-liner
  - L179 [advisory] `local-hypothesis-injection` in `theorem hasFDerivAt_relativeModularSupervolumeKreinQuadraticPotential` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L181 [advisory] `local-hypothesis-injection` in `theorem hasFDerivAt_relativeModularSupervolumeKreinQuadraticPotential` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L191 [soft] `skeletal-proof` in `theorem hasFDerivAt_relativeModularSupervolumeKreinGradient` — proof appears to close via minimal tactic one-liner
  - L208 [soft] `skeletal-proof` in `theorem relativeModularSupervolumeKreinHessian_bilin_eq_krein_form` — proof appears to close via minimal tactic one-liner
  - L222 [advisory] `bridge-shaped-declaration` in `theorem relativeModularSupervolume_concrete_secondDerivative_Krein_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L307 [soft] `skeletal-proof` in `theorem relativeModularSupervolumeKreinQuadraticPotential_realDoubled_eq_hestenes_splitQ11` — proof appears to close via minimal tactic one-liner
  - L323 [advisory] `bridge-shaped-declaration` in `theorem relativeModularSupervolume_Hestenes_realDoubled_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L371 [soft] `law-field-locker` in `structure-field RelativeModularSupervolumeKreinHessianLift.drazinCut` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L373 [soft] `law-field-locker` in `structure-field RelativeModularSupervolumeKreinHessianLift.modularAdjointFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L377 [soft] `law-field-locker` in `structure-field RelativeModularSupervolumeKreinHessianLift.liftedSupervolumePotential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L379 [soft] `law-field-locker` in `structure-field RelativeModularSupervolumeKreinHessianLift.secondVariation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L381 [soft] `law-field-locker` in `structure-field RelativeModularSupervolumeKreinHessianLift.sinkhornPerelmanMetric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L383 [soft] `law-field-locker` in `structure-field RelativeModularSupervolumeKreinHessianLift.lifted_base_eq_relativeModularSupervolumePotential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L388 [soft] `law-field-locker` in `structure-field RelativeModularSupervolumeKreinHessianLift.secondVariation_eq_kreinInner` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L395 [soft] `law-field-locker` in `structure-field RelativeModularSupervolumeKreinHessianLift.sinkhornPerelmanMetric_eq_secondVariation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L400 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L400 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L448 [advisory] `bridge-shaped-declaration` in `theorem relativeModularSupervolume_secondVariation_Krein_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L474 [soft] `law-field-locker` in `structure-field SplitModularSupervolumeShadow.parityTrace_eq_logBerezinian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L478 [soft] `simp-law-injection` in `simp-declaration parityTrace_eq_logBerezinianReg` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

