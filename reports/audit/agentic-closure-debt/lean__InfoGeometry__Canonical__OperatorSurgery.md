# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:37.406742+00:00`
Root: `lean/InfoGeometry/Canonical/OperatorSurgery.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **32**
- Hard: **0**
- Soft: **20**
- Advisory: **12**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/OperatorSurgery.lean` | `advisory` | 52 | 0 | 20 | 12 | 32 |

## Findings by file

### `lean/InfoGeometry/Canonical/OperatorSurgery.lean`
- module: `InfoGeometry.Canonical.OperatorSurgery`
- status: `advisory`
- debt_score: `52`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L18 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L27 [advisory] `existential-packaging` in `structure DrazinInverseWitness` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L28 [soft] `law-field-locker` in `structure-field DrazinInverseWitness.drazin_outer` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L30 [soft] `law-field-locker` in `structure-field DrazinInverseWitness.commute` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L32 [soft] `law-field-locker` in `structure-field DrazinInverseWitness.drazin_power` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L42 [advisory] `existential-packaging` in `structure DrazinSurgeryWitness` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L45 [soft] `law-field-locker` in `structure-field DrazinSurgeryWitness.is_idempotent_core` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [soft] `law-field-locker` in `structure-field DrazinSurgeryWitness.is_idempotent_nil` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [soft] `law-field-locker` in `structure-field DrazinSurgeryWitness.is_disjoint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [soft] `law-field-locker` in `structure-field DrazinSurgeryWitness.is_partition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L53 [soft] `law-field-locker` in `structure-field DrazinSurgeryWitness.commutes_with_A` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [soft] `law-field-locker` in `structure-field DrazinSurgeryWitness.nil_eventually_annihilated` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L61 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L62 [soft] `simp-law-injection` in `simp-declaration core_idempotent` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L70 [soft] `simp-law-injection` in `simp-declaration nil_idempotent` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L78 [soft] `simp-law-injection` in `simp-declaration core_nil_disjoint` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L98 [advisory] `existential-packaging` in `theorem nil_power_annihilates` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L103 [advisory] `existential-packaging` in `theorem nil_power_annihilates_apply` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L121 [soft] `skeletal-proof` in `theorem core_add_nil_apply` — proof appears to close via minimal tactic one-liner
  - L129 [soft] `simp-law-injection` in `simp-declaration nil_core_disjoint` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L136 [soft] `skeletal-proof` in `theorem nil_core_disjoint` — proof appears to close via minimal tactic one-liner
  - L174 [soft] `skeletal-proof` in `theorem nil_core_apply_eq_zero` — proof appears to close via minimal tactic one-liner
  - L224 [advisory] `existential-packaging` in `def ofDrazinInverse` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L228 [advisory] `local-hypothesis-injection` in `def ofDrazinInverse` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L237 [advisory] `local-hypothesis-injection` in `def ofDrazinInverse` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L242 [advisory] `local-hypothesis-injection` in `def ofDrazinInverse` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L330 [soft] `simp-law-injection` in `simp-declaration identitySplit_projector_core` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L332 [soft] `skeletal-proof` in `theorem identitySplit_projector_core` — proof appears to close via minimal tactic one-liner
  - L335 [soft] `simp-law-injection` in `simp-declaration identitySplit_projector_nil` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L337 [soft] `skeletal-proof` in `theorem identitySplit_projector_nil` — proof appears to close via minimal tactic one-liner
  - L340 [advisory] `existential-packaging` in `theorem exists_identitySplit` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

