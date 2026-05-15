# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:05.347425+00:00`
Root: `lean/InfoGeometry/Canonical/DrazinSupercharge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **72**
- Hard: **0**
- Soft: **39**
- Advisory: **33**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DrazinSupercharge.lean` | `advisory` | 111 | 0 | 39 | 33 | 72 |

## Findings by file

### `lean/InfoGeometry/Canonical/DrazinSupercharge.lean`
- module: `InfoGeometry.Canonical.DrazinSupercharge`
- status: `advisory`
- debt_score: `111`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L15 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L40 [advisory] `existential-packaging` in `def IsScalarOperator` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L56 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L81 [soft] `skeletal-proof` in `theorem supercharge_eq_commutator_spectralProjector_GammaG` — proof appears to close via minimal tactic one-liner
  - L141 [soft] `skeletal-proof` in `theorem supercharge_eq_commutator_spectralProjector_sigma_of_geometricMismatch_eq_zero` — proof appears to close via minimal tactic one-liner
  - L167 [soft] `skeletal-proof` in `theorem supercharge_eq_two_smul_commutatorK_spectralProjector_dilationGap` — proof appears to close via minimal tactic one-liner
  - L171 [soft] `skeletal-proof` in `theorem supercharge_is_odd` — proof appears to close via minimal tactic one-liner
  - L179 [advisory] `local-hypothesis-injection` in `theorem supercharge_is_odd` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L182 [advisory] `local-hypothesis-injection` in `theorem supercharge_is_odd` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L205 [soft] `skeletal-proof` in `theorem supercharge_is_oddK` — proof appears to close via minimal tactic one-liner
  - L208 [soft] `skeletal-proof` in `theorem supercharge_isSpectralNonCompact` — proof appears to close via minimal tactic one-liner
  - L218 [advisory] `local-hypothesis-injection` in `theorem supercharge_isSpectralNonCompact` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L222 [advisory] `local-hypothesis-injection` in `theorem supercharge_isSpectralNonCompact` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L257 [soft] `skeletal-proof` in `theorem spectralProjector_mul_regularRestrictedSuperHamiltonian` — proof appears to close via minimal tactic one-liner
  - L276 [soft] `skeletal-proof` in `theorem regularRestrictedSuperHamiltonian_mul_spectralProjector` — proof appears to close via minimal tactic one-liner
  - L295 [soft] `skeletal-proof` in `theorem spectralComplementaryProjector_mul_regularRestrictedSuperHamiltonian_eq_zero` — proof appears to close via minimal tactic one-liner
  - L312 [soft] `skeletal-proof` in `theorem regularRestrictedSuperHamiltonian_mul_spectralComplementaryProjector_eq_zero` — proof appears to close via minimal tactic one-liner
  - L335 [soft] `skeletal-proof` in `theorem supercharge_mul_GammaS_eq_neg` — proof appears to close via minimal tactic one-liner
  - L361 [soft] `law-field-locker` in `structure-field ChiralSupertraceReadout.readout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L362 [soft] `law-field-locker` in `structure-field ChiralSupertraceReadout.chiral_cyclic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L379 [soft] `skeletal-proof` in `theorem chiralSupertrace_supercharge_eq_zero` — proof appears to close via minimal tactic one-liner
  - L401 [soft] `skeletal-proof` in `theorem superHamiltonian_commutes_GammaS` — proof appears to close via minimal tactic one-liner
  - L410 [advisory] `local-hypothesis-injection` in `theorem superHamiltonian_commutes_GammaS` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L438 [soft] `skeletal-proof` in `theorem regularRestrictedSuperHamiltonian_commutes_GammaS` — proof appears to close via minimal tactic one-liner
  - L441 [advisory] `local-hypothesis-injection` in `theorem regularRestrictedSuperHamiltonian_commutes_GammaS` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L445 [advisory] `local-hypothesis-injection` in `theorem regularRestrictedSuperHamiltonian_commutes_GammaS` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L485 [soft] `skeletal-proof` in `theorem regularRestrictedSuperHamiltonian_fixed_under_spectralGradingFlow` — proof appears to close via minimal tactic one-liner
  - L587 [soft] `skeletal-proof` in `theorem superHamiltonian_fixed_under_spectralGradingFlow` — proof appears to close via minimal tactic one-liner
  - L604 [soft] `skeletal-proof` in `theorem superHamiltonianK_isSpectralCompact` — proof appears to close via minimal tactic one-liner
  - L611 [soft] `skeletal-proof` in `theorem superHamiltonianK_fixed_under_spectralGradingFlow` — proof appears to close via minimal tactic one-liner
  - L617 [soft] `skeletal-proof` in `theorem superHamiltonian_commutes_spectralGradingFlow` — proof appears to close via minimal tactic one-liner
  - L720 [soft] `skeletal-proof` in `theorem canonicalDefectCentral_isDefectSupported` — proof appears to close via minimal tactic one-liner
  - L724 [advisory] `local-hypothesis-injection` in `theorem canonicalDefectCentral_isDefectSupported` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L738 [soft] `skeletal-proof` in `theorem canonicalDefectCentralK_isDefectSupportedK` — proof appears to close via minimal tactic one-liner
  - L748 [soft] `skeletal-proof` in `theorem spectralComplementaryProjector_not_scalar_of_nontrivial` — proof appears to close via minimal tactic one-liner
  - L757 [advisory] `local-hypothesis-injection` in `theorem spectralComplementaryProjector_not_scalar_of_nontrivial` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L768 [advisory] `local-hypothesis-injection` in `theorem spectralComplementaryProjector_not_scalar_of_nontrivial` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L771 [advisory] `local-hypothesis-injection` in `theorem spectralComplementaryProjector_not_scalar_of_nontrivial` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L773 [advisory] `local-hypothesis-injection` in `theorem spectralComplementaryProjector_not_scalar_of_nontrivial` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L775 [advisory] `local-hypothesis-injection` in `theorem spectralComplementaryProjector_not_scalar_of_nontrivial` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L789 [soft] `skeletal-proof` in `theorem spectralComplementaryProjector_not_scalar_of_nontrivialK` — proof appears to close via minimal tactic one-liner
  - L799 [soft] `skeletal-proof` in `theorem canonicalKineticPart_hasVanishingDefectBlock` — proof appears to close via minimal tactic one-liner
  - L803 [advisory] `local-hypothesis-injection` in `theorem canonicalKineticPart_hasVanishingDefectBlock` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L807 [advisory] `local-hypothesis-injection` in `theorem canonicalKineticPart_hasVanishingDefectBlock` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L825 [soft] `skeletal-proof` in `theorem canonicalKineticPartK_hasVanishingDefectBlockK` — proof appears to close via minimal tactic one-liner
  - L834 [soft] `skeletal-proof` in `theorem spectralComplementaryProjector_mul_eq_of_isDefectSupported` — proof appears to close via minimal tactic one-liner
  - L857 [soft] `skeletal-proof` in `theorem mul_spectralComplementaryProjector_eq_of_isDefectSupported` — proof appears to close via minimal tactic one-liner
  - L880 [soft] `skeletal-proof` in `theorem spectralProjector_mul_eq_zero_of_isDefectSupported` — proof appears to close via minimal tactic one-liner
  - L900 [soft] `skeletal-proof` in `theorem mul_spectralProjector_eq_zero_of_isDefectSupported` — proof appears to close via minimal tactic one-liner
  - L920 [soft] `skeletal-proof` in `theorem isDrazinSpectralCentral_of_isDefectSupported` — proof appears to close via minimal tactic one-liner
  - L926 [advisory] `local-hypothesis-injection` in `theorem isDrazinSpectralCentral_of_isDefectSupported` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L929 [advisory] `local-hypothesis-injection` in `theorem isDrazinSpectralCentral_of_isDefectSupported` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L936 [advisory] `local-hypothesis-injection` in `theorem isDrazinSpectralCentral_of_isDefectSupported` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L939 [advisory] `local-hypothesis-injection` in `theorem isDrazinSpectralCentral_of_isDefectSupported` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L950 [soft] `skeletal-proof` in `theorem commute_GammaS_of_isDrazinSpectralCentral` — proof appears to close via minimal tactic one-liner
  - L988 [soft] `skeletal-proof` in `theorem canonicalDefectCentralK_isDrazinSpectralCentralK` — proof appears to close via minimal tactic one-liner
  - L995 [soft] `skeletal-proof` in `theorem canonicalDefectCentralK_isDrazinLaneCentralK` — proof appears to close via minimal tactic one-liner
  - L1036 [soft] `skeletal-proof` in `theorem superHamiltonianK_eq_canonicalKineticPartK_plus_canonicalDefectCentralK` — proof appears to close via minimal tactic one-liner
  - L1046 [advisory] `existential-packaging` in `theorem exists_superHamiltonian_canonical_split` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1058 [advisory] `existential-packaging` in `theorem exists_superHamiltonian_canonical_splitK` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1071 [advisory] `existential-packaging` in `theorem exists_superHamiltonian_canonical_split_with_spectral_centrality` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1085 [advisory] `existential-packaging` in `theorem exists_superHamiltonian_canonical_split_with_spectral_centralityK` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1099 [advisory] `existential-packaging` in `theorem exists_superHamiltonian_canonical_split_with_drazin_lane_centrality` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1115 [advisory] `existential-packaging` in `theorem exists_superHamiltonian_canonical_split_with_drazin_lane_centralityK` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1171 [soft] `skeletal-proof` in `theorem canonicalKineticPart_eq_of_split` — proof appears to close via minimal tactic one-liner
  - L1177 [advisory] `local-hypothesis-injection` in `theorem canonicalKineticPart_eq_of_split` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1179 [advisory] `local-hypothesis-injection` in `theorem canonicalKineticPart_eq_of_split` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1236 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L1238 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L1270 [soft] `skeletal-proof` in `theorem operatorialCentralDefectShadow_not_scalar_of_nonzero_charge_of_nontrivial_defect_projector` — proof appears to close via minimal tactic one-liner
  - L1326 [soft] `skeletal-proof` in `theorem operatorialCentralDefectShadow_isDefectSupported` — proof appears to close via minimal tactic one-liner

