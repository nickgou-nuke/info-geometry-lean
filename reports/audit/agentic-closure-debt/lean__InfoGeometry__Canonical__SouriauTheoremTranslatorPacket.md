# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:58.593613+00:00`
Root: `lean/InfoGeometry/Canonical/SouriauTheoremTranslatorPacket.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **35**
- Hard: **0**
- Soft: **3**
- Advisory: **32**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SouriauTheoremTranslatorPacket.lean` | `advisory` | 38 | 0 | 3 | 32 | 35 |

## Findings by file

### `lean/InfoGeometry/Canonical/SouriauTheoremTranslatorPacket.lean`
- module: `InfoGeometry.Canonical.SouriauTheoremTranslatorPacket`
- status: `advisory`
- debt_score: `38`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L84 [soft] `law-field-locker` in `structure-field EntropyFisherInverseGate.entropy_hessian_eq_fisher_inverse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L121 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L123 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L133 [advisory] `bridge-shaped-declaration` in `theorem claimD_operatorLegendre_inverseHessian_eq_inverseFisher_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L161 [advisory] `existential-packaging` in `structure StrictOnsagerEquilibriumGate` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L164 [soft] `law-field-locker` in `structure-field StrictOnsagerEquilibriumGate.forceIsZero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L165 [soft] `law-field-locker` in `structure-field StrictOnsagerEquilibriumGate.entropyProduction_eq_zero_iff_force_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L173 [advisory] `existential-packaging` in `theorem claimE_entropyProduction_eq_zero_iff_force_zero` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L189 [advisory] `existential-packaging` in `theorem claimA_massieu_eq_log_partition` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L205 [advisory] `existential-packaging` in `theorem claimB_firstDerivatives_eq_moments` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L225 [advisory] `existential-packaging` in `theorem claimC_hessian_eq_fisher_eq_covariance` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L258 [advisory] `bridge-shaped-declaration` in `theorem claimD_fenchelLegendre_contact_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L258 [advisory] `existential-packaging` in `theorem claimD_fenchelLegendre_contact_packet` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L278 [advisory] `existential-packaging` in `theorem claimE_entropyProduction_nonneg_of_PSD` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L293 [advisory] `existential-packaging` in `theorem claimE_entropyProduction_nonneg_of_det_nonneg` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L306 [advisory] `existential-packaging` in `theorem claimE_entropyProduction_eq_zero_iff_force_zero_of_PD` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L327 [advisory] `existential-packaging` in `theorem structuredSouriauTranslatorPacket` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L365 [advisory] `existential-packaging` in `theorem structuredSouriauTranslatorPacket_of_det_nonneg` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L411 [advisory] `bridge-shaped-declaration` in `theorem claimK_kktEntropyStationarity_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L477 [advisory] `bridge-shaped-declaration` in `theorem claimF_superSouriauFermionGas_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L543 [advisory] `bridge-shaped-declaration` in `theorem claimF_superSouriauFermionGas_packet_ofIdentityBalancedStress` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L633 [advisory] `bridge-shaped-declaration` in `theorem claimG_infiniteSuperCoadjointMetriplectic_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L652 [advisory] `local-hypothesis-injection` in `theorem claimG_infiniteSuperCoadjointMetriplectic_packet` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L676 [advisory] `bridge-shaped-declaration` in `theorem claimT_splitCl44_TKK_JordanLie_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L721 [advisory] `bridge-shaped-declaration` in `theorem claimM_coadjointLeaf_Casimir_transverseOnsager_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L744 [advisory] `bridge-shaped-declaration` in `theorem claimM_coadjointLeaf_Casimir_transverseOnsager_square_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L794 [advisory] `existential-packaging` in `theorem structuredSouriauKKTTranslatorPacket` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L835 [advisory] `existential-packaging` in `theorem structuredSouriauKKTTranslatorPacket_ofExactResiduals` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L875 [advisory] `existential-packaging` in `theorem structuredSouriauKKTTranslatorPacket_ofExactResiduals_det_nonneg` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L919 [advisory] `existential-packaging` in `theorem analyticEnrichmentTranslatorPacket` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L942 [advisory] `bridge-shaped-declaration` in `theorem claimCD_fullCoadjointOrbit_hessian_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L965 [advisory] `bridge-shaped-declaration` in `theorem claimCD_fullCoadjointOrbit_strict_hessian_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L991 [advisory] `bridge-shaped-declaration` in `theorem claimCDE_fullCoadjointOrbit_hessian_metriplectic_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L1019 [advisory] `bridge-shaped-declaration` in `theorem claimCDE_fullCoadjointOrbit_strict_hessian_metriplectic_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

