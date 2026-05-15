# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:26.794531+00:00`
Root: `lean/InfoGeometry/Canonical/MajoranaJKOErgoBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **28**
- Hard: **0**
- Soft: **14**
- Advisory: **14**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/MajoranaJKOErgoBridge.lean` | `advisory` | 42 | 0 | 14 | 14 | 28 |

## Findings by file

### `lean/InfoGeometry/Canonical/MajoranaJKOErgoBridge.lean`
- module: `InfoGeometry.Canonical.MajoranaJKOErgoBridge`
- status: `advisory`
- debt_score: `42`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L76 [soft] `law-field-locker` in `structure-field MajoranaJKOErgoBridge.majorana` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L92 [soft] `law-field-locker` in `structure-field MajoranaJKOErgoBridge.encodeDensity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L96 [soft] `law-field-locker` in `structure-field MajoranaJKOErgoBridge.feasibleAlternative` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L100 [soft] `law-field-locker` in `structure-field MajoranaJKOErgoBridge.bayesUpdate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L104 [soft] `law-field-locker` in `structure-field MajoranaJKOErgoBridge.bayes_update_previous_eq_next` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L112 [soft] `law-field-locker` in `structure-field MajoranaJKOErgoBridge.jko_bayes_compatibility_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L126 [soft] `law-field-locker` in `structure-field MajoranaJKOErgoBridge.projection_orthogonality` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L159 [advisory] `bridge-shaped-declaration` in `theorem compatibility_valid` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L231 [soft] `simp-law-injection` in `simp-declaration encodedDivergence_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L304 [advisory] `bridge-shaped-declaration` in `theorem majorana_qgt_compat` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L361 [soft] `law-field-locker` in `structure-field OperatorJKOBayesMajoranaBridge.majorana` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L379 [soft] `law-field-locker` in `structure-field OperatorJKOBayesMajoranaBridge.feasibleAlternative` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L383 [soft] `law-field-locker` in `structure-field OperatorJKOBayesMajoranaBridge.projection_orthogonality` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L502 [soft] `law-field-locker` in `structure-field ScalarJKOParameters.tau_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L513 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L520 [soft] `skeletal-proof` in `theorem one_add_tau_pos` — proof appears to close via minimal tactic one-liner
  - L552 [advisory] `local-hypothesis-injection` in `theorem square_coefficient_pos` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L554 [advisory] `local-hypothesis-injection` in `theorem square_coefficient_pos` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L583 [advisory] `local-hypothesis-injection` in `theorem step_minimizes` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L586 [advisory] `local-hypothesis-injection` in `theorem step_minimizes` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L590 [soft] `skeletal-proof` in `theorem eq_step_of_equal_value` — proof appears to close via minimal tactic one-liner
  - L598 [advisory] `local-hypothesis-injection` in `theorem eq_step_of_equal_value` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L602 [advisory] `local-hypothesis-injection` in `theorem eq_step_of_equal_value` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L610 [advisory] `local-hypothesis-injection` in `theorem eq_step_of_equal_value` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L616 [advisory] `local-hypothesis-injection` in `theorem eq_step_of_equal_value` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L634 [advisory] `local-hypothesis-injection` in `theorem step_unique_minimizer` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L669 [advisory] `existential-packaging` in `def MajoranaJKOErgoBridgeOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

