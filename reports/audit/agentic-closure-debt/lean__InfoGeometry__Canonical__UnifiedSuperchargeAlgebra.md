# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:08.480116+00:00`
Root: `lean/InfoGeometry/Canonical/UnifiedSuperchargeAlgebra.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **43**
- Hard: **0**
- Soft: **27**
- Advisory: **16**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/UnifiedSuperchargeAlgebra.lean` | `advisory` | 70 | 0 | 27 | 16 | 43 |

## Findings by file

### `lean/InfoGeometry/Canonical/UnifiedSuperchargeAlgebra.lean`
- module: `InfoGeometry.Canonical.UnifiedSuperchargeAlgebra`
- status: `advisory`
- debt_score: `70`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L24 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L26 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L27 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L49 [soft] `law-field-locker` in `structure-field UnifiedSuperchargePackage.primitive` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L53 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L53 [soft] `section-law-variable` in `variable U` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L97 [soft] `skeletal-proof` in `theorem primitive_phaseChannel_eq_phaseAxis` — proof appears to close via minimal tactic one-liner
  - L102 [advisory] `local-hypothesis-injection` in `theorem primitive_phaseChannel_eq_phaseAxis` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L127 [soft] `skeletal-proof` in `theorem projected_supercharge_is_odd` — proof appears to close via minimal tactic one-liner
  - L134 [soft] `skeletal-proof` in `theorem projected_hamiltonian_is_even` — proof appears to close via minimal tactic one-liner
  - L142 [soft] `skeletal-proof` in `theorem projected_supercharge_eq_two_commutator` — proof appears to close via minimal tactic one-liner
  - L150 [soft] `skeletal-proof` in `theorem projected_supercharge_eq_sub_chiral` — proof appears to close via minimal tactic one-liner
  - L155 [soft] `skeletal-proof` in `theorem projected_left_eq_commutator_PD_PL` — proof appears to close via minimal tactic one-liner
  - L161 [soft] `skeletal-proof` in `theorem projected_right_eq_commutator_PD_PR` — proof appears to close via minimal tactic one-liner
  - L167 [soft] `skeletal-proof` in `theorem projected_hamiltonian_eq_square` — proof appears to close via minimal tactic one-liner
  - L284 [soft] `skeletal-proof` in `theorem drazinTranslationCentralDefectPacket_fst` — proof appears to close via minimal tactic one-liner
  - L289 [soft] `skeletal-proof` in `theorem drazinTranslationCentralDefectPacket_snd` — proof appears to close via minimal tactic one-liner
  - L306 [soft] `law-field-locker` in `structure-field DrazinSupergradedTranslationPacket.oddOdd_bracket_eq_two_smul_translation_plus_central` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L308 [soft] `law-field-locker` in `structure-field DrazinSupergradedTranslationPacket.central_eq_defect` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L312 [soft] `skeletal-proof` in `theorem drazinCentralCandidate_eq_defectCandidate` — proof appears to close via minimal tactic one-liner
  - L321 [soft] `skeletal-proof` in `theorem projected_oddOdd_bracket_eq_two_smul_translation_plus_central` — proof appears to close via minimal tactic one-liner
  - L357 [advisory] `existential-packaging` in `theorem drazinSupergradedTranslationPacket_ofOwners` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L388 [soft] `skeletal-proof` in `theorem drazinMajoranaConjugateCandidate_eq_QD_of_commute_chi` — proof appears to close via minimal tactic one-liner
  - L467 [soft] `skeletal-proof` in `theorem drazinKramersConjugateCandidate_is_odd_of_commute_GammaS` — proof appears to close via minimal tactic one-liner
  - L518 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L520 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L527 [soft] `law-field-locker` in `structure-field TransportedSuperchargePackage.V` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L530 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L530 [soft] `section-law-variable` in `variable T` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L546 [soft] `skeletal-proof` in `theorem deriv_QPi_t` — proof appears to close via minimal tactic one-liner
  - L554 [soft] `skeletal-proof` in `theorem deriv_QJ_t` — proof appears to close via minimal tactic one-liner
  - L562 [soft] `skeletal-proof` in `theorem deriv2_QPi_t_eq_operatorInformationHessian` — proof appears to close via minimal tactic one-liner
  - L572 [soft] `skeletal-proof` in `theorem deriv2_QPi_t_eq_metricPart_add_half_curvaturePart` — proof appears to close via minimal tactic one-liner
  - L603 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L615 [soft] `law-field-locker` in `structure-field TopologicalCentralChargePackage.hZop` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L619 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L619 [soft] `section-law-variable` in `variable Z` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L626 [soft] `skeletal-proof` in `theorem Zop_transport_invariant` — proof appears to close via minimal tactic one-liner
  - L657 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L702 [advisory] `bridge-shaped-declaration` in `theorem unified_cross_family_compatibility` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L756 [advisory] `existential-packaging` in `theorem unified_sources_sinks_onsager_with_internal_central_split` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L835 [advisory] `existential-packaging` in `theorem unified_internal_split_with_operatorial_shadow` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

