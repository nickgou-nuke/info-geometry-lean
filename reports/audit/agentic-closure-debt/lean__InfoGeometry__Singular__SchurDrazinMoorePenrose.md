# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:40.482519+00:00`
Root: `lean/InfoGeometry/Singular/SchurDrazinMoorePenrose.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **37**
- Hard: **0**
- Soft: **25**
- Advisory: **12**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Singular/SchurDrazinMoorePenrose.lean` | `advisory` | 62 | 0 | 25 | 12 | 37 |

## Findings by file

### `lean/InfoGeometry/Singular/SchurDrazinMoorePenrose.lean`
- module: `InfoGeometry.Singular.SchurDrazinMoorePenrose`
- status: `advisory`
- debt_score: `62`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L48 [soft] `law-field-locker` in `structure-field ResolutionOfIdentityLedger.eigenvalue` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [soft] `law-field-locker` in `structure-field ResolutionOfIdentityLedger.spectralProjector` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L54 [soft] `law-field-locker` in `structure-field ResolutionOfIdentityLedger.is_zero_mode` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L57 [soft] `law-field-locker` in `structure-field ResolutionOfIdentityLedger.projector_idempotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L61 [soft] `law-field-locker` in `structure-field ResolutionOfIdentityLedger.projector_orthogonal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L65 [soft] `law-field-locker` in `structure-field ResolutionOfIdentityLedger.projector_sum_identity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L69 [soft] `law-field-locker` in `structure-field ResolutionOfIdentityLedger.projector_self_adjoint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L73 [soft] `law-field-locker` in `structure-field ResolutionOfIdentityLedger.spectral_expansion_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L83 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L158 [soft] `skeletal-proof` in `theorem drazinRegularProjector_idempotent` — proof appears to close via minimal tactic one-liner
  - L168 [soft] `skeletal-proof` in `theorem one_sub_idempotent` — proof appears to close via minimal tactic one-liner
  - L194 [soft] `skeletal-proof` in `theorem drazinRegular_add_drazinNull` — proof appears to close via minimal tactic one-liner
  - L239 [soft] `skeletal-proof` in `theorem moorePenroseRangeProjector_idempotent` — proof appears to close via minimal tactic one-liner
  - L248 [soft] `skeletal-proof` in `theorem moorePenroseRangeProjector_self_adjoint` — proof appears to close via minimal tactic one-liner
  - L256 [soft] `skeletal-proof` in `theorem moorePenroseCoimageProjector_idempotent` — proof appears to close via minimal tactic one-liner
  - L286 [soft] `skeletal-proof` in `theorem moorePenroseKernelProjector_self_adjoint` — proof appears to close via minimal tactic one-liner
  - L330 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L417 [advisory] `existential-packaging` in `theorem exists_singularDrazinInverse_global_endCLM` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L417 [soft] `skeletal-proof` in `theorem exists_singularDrazinInverse_global_endCLM` — proof appears to close via minimal tactic one-liner
  - L433 [advisory] `local-hypothesis-injection` in `theorem exists_singularDrazinInverse_global_endCLM` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L435 [advisory] `local-hypothesis-injection` in `theorem exists_singularDrazinInverse_global_endCLM` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L437 [advisory] `local-hypothesis-injection` in `theorem exists_singularDrazinInverse_global_endCLM` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L445 [advisory] `local-hypothesis-injection` in `theorem exists_singularDrazinInverse_global_endCLM` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L451 [advisory] `local-hypothesis-injection` in `theorem exists_singularDrazinInverse_global_endCLM` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L454 [advisory] `local-hypothesis-injection` in `theorem exists_singularDrazinInverse_global_endCLM` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L490 [soft] `law-field-locker` in `structure-field SchurDrazinNormalForm.schur_normal_form_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L548 [soft] `law-field-locker` in `structure-field SVDMoorePenroseNormalForm.svd_normal_form_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L595 [soft] `law-field-locker` in `structure-field KreinMoorePenroseInverse.sharp` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L598 [soft] `law-field-locker` in `structure-field KreinMoorePenroseInverse.aba_eq_a` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L601 [soft] `law-field-locker` in `structure-field KreinMoorePenroseInverse.bab_eq_b` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L604 [soft] `law-field-locker` in `structure-field KreinMoorePenroseInverse.range_sharp_self` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L607 [soft] `law-field-locker` in `structure-field KreinMoorePenroseInverse.coimage_sharp_self` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L614 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L623 [soft] `skeletal-proof` in `theorem rangeProjector_idempotent` — proof appears to close via minimal tactic one-liner
  - L632 [soft] `skeletal-proof` in `theorem coimageProjector_idempotent` — proof appears to close via minimal tactic one-liner
  - L667 [advisory] `existential-packaging` in `theorem drazinMoorePenroseLedgerOwnerTarget_hilbertFinite` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

