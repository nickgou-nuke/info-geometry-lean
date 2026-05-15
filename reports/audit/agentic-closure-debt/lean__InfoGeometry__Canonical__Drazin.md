# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:01.209495+00:00`
Root: `lean/InfoGeometry/Canonical/Drazin.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **80**
- Hard: **0**
- Soft: **47**
- Advisory: **33**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/Drazin.lean` | `advisory` | 127 | 0 | 47 | 33 | 80 |

## Findings by file

### `lean/InfoGeometry/Canonical/Drazin.lean`
- module: `InfoGeometry.Canonical.Drazin`
- status: `advisory`
- debt_score: `127`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [advisory] `local-hypothesis-injection` in `theorem of_idempotent` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L87 [advisory] `local-hypothesis-injection` in `theorem complementaryProjection_is_idempotent` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L96 [advisory] `local-hypothesis-injection` in `theorem projection_mul_complementaryProjection` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L105 [advisory] `local-hypothesis-injection` in `theorem complementaryProjection_mul_projection` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L139 [advisory] `local-hypothesis-injection` in `theorem complementaryProjection_comm_self` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L178 [advisory] `local-hypothesis-injection` in `theorem complementaryProjection_mul_power_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L189 [soft] `skeletal-proof` in `theorem power_le` — proof appears to close via minimal tactic one-liner
  - L205 [advisory] `local-hypothesis-injection` in `theorem fittingNilpotentPart_pow_succ_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L220 [advisory] `local-hypothesis-injection` in `theorem fittingNilpotentPart_pow_succ_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L260 [soft] `skeletal-proof` in `theorem star_isDrazinInverse_of_selfAdjoint` — proof appears to close via minimal tactic one-liner
  - L264 [advisory] `local-hypothesis-injection` in `theorem star_isDrazinInverse_of_selfAdjoint` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L312 [soft] `skeletal-proof` in `theorem projection_isStarProjection_of_selfAdjoint` — proof appears to close via minimal tactic one-liner
  - L318 [advisory] `local-hypothesis-injection` in `theorem projection_isStarProjection_of_selfAdjoint` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L371 [advisory] `local-hypothesis-injection` in `lemma add_pow_succ_of_orthogonal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L373 [advisory] `local-hypothesis-injection` in `lemma add_pow_succ_of_orthogonal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L390 [advisory] `local-hypothesis-injection` in `lemma core_pow_succ_succ_mul_inverse` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L443 [advisory] `local-hypothesis-injection` in `theorem of_core_nilpotent_split` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L446 [advisory] `local-hypothesis-injection` in `theorem of_core_nilpotent_split` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L448 [advisory] `local-hypothesis-injection` in `theorem of_core_nilpotent_split` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L476 [soft] `law-field-locker` in `structure-field DrazinFittingDecomposition.decompose` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L477 [soft] `law-field-locker` in `structure-field DrazinFittingDecomposition.core_mul_nil` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L478 [soft] `law-field-locker` in `structure-field DrazinFittingDecomposition.nil_mul_core` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L479 [soft] `law-field-locker` in `structure-field DrazinFittingDecomposition.core_comm_inverse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L480 [soft] `law-field-locker` in `structure-field DrazinFittingDecomposition.nil_mul_inverse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L481 [soft] `law-field-locker` in `structure-field DrazinFittingDecomposition.inverse_mul_nil` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L482 [soft] `law-field-locker` in `structure-field DrazinFittingDecomposition.core_inverse_core` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L483 [soft] `law-field-locker` in `structure-field DrazinFittingDecomposition.inverse_core_inverse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L484 [soft] `law-field-locker` in `structure-field DrazinFittingDecomposition.nilpotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L494 [advisory] `existential-packaging` in `theorem exists_drazinInverse_of_fittingDecomposition` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L529 [soft] `law-field-locker` in `structure-field ContinuousDrazinFittingBlockData.corePart` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L530 [soft] `law-field-locker` in `structure-field ContinuousDrazinFittingBlockData.nilPart` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L531 [soft] `law-field-locker` in `structure-field ContinuousDrazinFittingBlockData.inversePart` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L533 [soft] `law-field-locker` in `structure-field ContinuousDrazinFittingBlockData.decompose` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L534 [soft] `law-field-locker` in `structure-field ContinuousDrazinFittingBlockData.core_mul_nil` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L535 [soft] `law-field-locker` in `structure-field ContinuousDrazinFittingBlockData.nil_mul_core` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L536 [soft] `law-field-locker` in `structure-field ContinuousDrazinFittingBlockData.core_comm_inverse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L537 [soft] `law-field-locker` in `structure-field ContinuousDrazinFittingBlockData.nil_mul_inverse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L538 [soft] `law-field-locker` in `structure-field ContinuousDrazinFittingBlockData.inverse_mul_nil` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L539 [soft] `law-field-locker` in `structure-field ContinuousDrazinFittingBlockData.core_inverse_core` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L540 [soft] `law-field-locker` in `structure-field ContinuousDrazinFittingBlockData.inverse_core_inverse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L541 [soft] `law-field-locker` in `structure-field ContinuousDrazinFittingBlockData.nilpotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L577 [advisory] `existential-packaging` in `theorem exists_drazinInverse` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L603 [soft] `law-field-locker` in `structure-field ContinuousDrazinFittingSubmoduleSplit.Pcore` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L604 [soft] `law-field-locker` in `structure-field ContinuousDrazinFittingSubmoduleSplit.Pnil` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L605 [soft] `law-field-locker` in `structure-field ContinuousDrazinFittingSubmoduleSplit.Dcore` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L607 [soft] `law-field-locker` in `structure-field ContinuousDrazinFittingSubmoduleSplit.Pcore_range` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L608 [soft] `law-field-locker` in `structure-field ContinuousDrazinFittingSubmoduleSplit.Pnil_range` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L609 [soft] `law-field-locker` in `structure-field ContinuousDrazinFittingSubmoduleSplit.projections_sum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L610 [soft] `law-field-locker` in `structure-field ContinuousDrazinFittingSubmoduleSplit.projections_core_nil` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L611 [soft] `law-field-locker` in `structure-field ContinuousDrazinFittingSubmoduleSplit.projections_nil_core` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L612 [soft] `law-field-locker` in `structure-field ContinuousDrazinFittingSubmoduleSplit.A_comm_core` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L613 [soft] `law-field-locker` in `structure-field ContinuousDrazinFittingSubmoduleSplit.A_comm_nil` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L614 [soft] `law-field-locker` in `structure-field ContinuousDrazinFittingSubmoduleSplit.core_comm_inverse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L615 [soft] `law-field-locker` in `structure-field ContinuousDrazinFittingSubmoduleSplit.nil_projection_mul_inverse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L616 [soft] `law-field-locker` in `structure-field ContinuousDrazinFittingSubmoduleSplit.inverse_mul_nil_projection` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L617 [soft] `law-field-locker` in `structure-field ContinuousDrazinFittingSubmoduleSplit.core_inverse_core` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L618 [soft] `law-field-locker` in `structure-field ContinuousDrazinFittingSubmoduleSplit.inverse_core_inverse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L619 [soft] `law-field-locker` in `structure-field ContinuousDrazinFittingSubmoduleSplit.nilpotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L710 [advisory] `existential-packaging` in `theorem exists_drazinInverse` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L719 [soft] `skeletal-proof` in `lemma inverse_eq_pow_mul_pow` — proof appears to close via minimal tactic one-liner
  - L724 [advisory] `local-hypothesis-injection` in `lemma inverse_eq_pow_mul_pow` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L730 [advisory] `local-hypothesis-injection` in `lemma inverse_eq_pow_mul_pow` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L755 [soft] `skeletal-proof` in `theorem core_eq_mul_projection` — proof appears to close via minimal tactic one-liner
  - L761 [soft] `skeletal-proof` in `theorem nilpotent_eq_mul_complementaryProjection` — proof appears to close via minimal tactic one-liner
  - L767 [soft] `skeletal-proof` in `theorem nilpotent_comm_self` — proof appears to close via minimal tactic one-liner
  - L769 [advisory] `local-hypothesis-injection` in `theorem nilpotent_comm_self` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L783 [soft] `skeletal-proof` in `theorem fitting_decomposition` — proof appears to close via minimal tactic one-liner
  - L785 [advisory] `local-hypothesis-injection` in `theorem fitting_decomposition` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L797 [soft] `skeletal-proof` in `theorem core_mul_nilpotent_eq_zero` — proof appears to close via minimal tactic one-liner
  - L801 [advisory] `local-hypothesis-injection` in `theorem core_mul_nilpotent_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L803 [advisory] `local-hypothesis-injection` in `theorem core_mul_nilpotent_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L805 [advisory] `local-hypothesis-injection` in `theorem core_mul_nilpotent_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L811 [advisory] `local-hypothesis-injection` in `theorem core_mul_nilpotent_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L822 [soft] `skeletal-proof` in `theorem nilpotent_mul_core_eq_zero` — proof appears to close via minimal tactic one-liner
  - L826 [advisory] `local-hypothesis-injection` in `theorem nilpotent_mul_core_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L828 [advisory] `local-hypothesis-injection` in `theorem nilpotent_mul_core_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L830 [advisory] `local-hypothesis-injection` in `theorem nilpotent_mul_core_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L836 [advisory] `local-hypothesis-injection` in `theorem nilpotent_mul_core_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L843 [advisory] `local-hypothesis-injection` in `theorem nilpotent_mul_core_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

