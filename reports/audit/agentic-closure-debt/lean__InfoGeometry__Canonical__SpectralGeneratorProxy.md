# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:59.275293+00:00`
Root: `lean/InfoGeometry/Canonical/SpectralGeneratorProxy.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **38**
- Hard: **0**
- Soft: **26**
- Advisory: **12**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SpectralGeneratorProxy.lean` | `advisory` | 64 | 0 | 26 | 12 | 38 |

## Findings by file

### `lean/InfoGeometry/Canonical/SpectralGeneratorProxy.lean`
- module: `InfoGeometry.Canonical.SpectralGeneratorProxy`
- status: `advisory`
- debt_score: `64`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L47 [soft] `skeletal-proof` in `theorem axis` — proof appears to close via minimal tactic one-liner
  - L86 [soft] `skeletal-proof` in `theorem sub` — proof appears to close via minimal tactic one-liner
  - L138 [soft] `law-field-locker` in `structure-field PhaseResolventDatum.denom_right_inverse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L142 [soft] `law-field-locker` in `structure-field PhaseResolventDatum.denom_left_inverse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L150 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L173 [soft] `skeletal-proof` in `theorem denomInv_phase_linear` — proof appears to close via minimal tactic one-liner
  - L183 [advisory] `local-hypothesis-injection` in `theorem denomInv_phase_linear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L185 [advisory] `local-hypothesis-injection` in `theorem denomInv_phase_linear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L191 [advisory] `local-hypothesis-injection` in `theorem denomInv_phase_linear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L212 [soft] `skeletal-proof` in `theorem denominator_right_inverse` — proof appears to close via minimal tactic one-liner
  - L217 [soft] `skeletal-proof` in `theorem denominator_left_inverse` — proof appears to close via minimal tactic one-liner
  - L244 [soft] `law-field-locker` in `structure-field BoundedTransformDatum.bounded_transform_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L254 [soft] `law-field-locker` in `structure-field BoundedTransformDatum.contraction_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L265 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L293 [soft] `law-field-locker` in `structure-field OperatorAdjointDatum.adj` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L295 [soft] `law-field-locker` in `structure-field OperatorAdjointDatum.adjoint_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L304 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L304 [soft] `section-law-variable` in `variable A` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L323 [soft] `law-field-locker` in `structure-field BoundedKasparovCycle.rep` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L328 [soft] `law-field-locker` in `structure-field BoundedKasparovCycle.adjoint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L334 [soft] `law-field-locker` in `structure-field BoundedKasparovCycle.rep_phase_linear` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L350 [soft] `law-field-locker` in `structure-field BoundedKasparovCycle.commutator_mod_compact` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L355 [soft] `law-field-locker` in `structure-field BoundedKasparovCycle.kasparov_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L367 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L367 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L416 [soft] `law-field-locker` in `structure-field KasparovAdmissibility.rep` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L418 [soft] `law-field-locker` in `structure-field KasparovAdmissibility.adjoint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L424 [soft] `law-field-locker` in `structure-field KasparovAdmissibility.rep_phase_linear` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L436 [soft] `law-field-locker` in `structure-field KasparovAdmissibility.commutator_mod_compact` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L441 [soft] `law-field-locker` in `structure-field KasparovAdmissibility.kasparov_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L454 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L454 [soft] `section-law-variable` in `variable Adm` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L473 [soft] `simp-law-injection` in `simp-declaration toBoundedKasparovCycle_F` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L478 [soft] `simp-law-injection` in `simp-declaration toBoundedKasparovCycle_rep` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L491 [advisory] `existential-packaging` in `def PhaseResolventOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L502 [advisory] `existential-packaging` in `def BoundedTransformOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L511 [advisory] `existential-packaging` in `def BoundedKasparovOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

