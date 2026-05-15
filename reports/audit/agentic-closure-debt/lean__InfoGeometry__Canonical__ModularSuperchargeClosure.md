# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:30.478307+00:00`
Root: `lean/InfoGeometry/Canonical/ModularSuperchargeClosure.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **55**
- Hard: **0**
- Soft: **35**
- Advisory: **20**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ModularSuperchargeClosure.lean` | `advisory` | 90 | 0 | 35 | 20 | 55 |

## Findings by file

### `lean/InfoGeometry/Canonical/ModularSuperchargeClosure.lean`
- module: `InfoGeometry.Canonical.ModularSuperchargeClosure`
- status: `advisory`
- debt_score: `90`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L49 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L51 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L165 [soft] `skeletal-proof` in `theorem supercharge_eq_commutator_spectralProjector_modularSign_add_commutator_spectralProjector_GammaG_sub_modularSign` — proof appears to close via minimal tactic one-liner
  - L184 [soft] `skeletal-proof` in `theorem supercharge_eq_commutator_spectralProjector_spectral_epsilon_add_commutator_spectralProjector_GammaG_sub_spectral_epsilon` — proof appears to close via minimal tactic one-liner
  - L217 [soft] `skeletal-proof` in `theorem superHamiltonian_eq_modularTransportGenerator_canonicalSeed` — proof appears to close via minimal tactic one-liner
  - L224 [advisory] `local-hypothesis-injection` in `theorem superHamiltonian_eq_modularTransportGenerator_canonicalSeed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L246 [soft] `skeletal-proof` in `theorem superHamiltonian_eq_modularTransportGenerator_lorentzBivectorSeed` — proof appears to close via minimal tactic one-liner
  - L281 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L281 [soft] `section-law-variable` in `variable M` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L297 [soft] `skeletal-proof` in `theorem hHD_eq_AMod` — proof appears to close via minimal tactic one-liner
  - L342 [soft] `skeletal-proof` in `theorem modularGenerator_eq_canonicalKinetic_plus_canonicalDefectCentral` — proof appears to close via minimal tactic one-liner
  - L365 [advisory] `existential-packaging` in `theorem exists_modularGenerator_split_with_drazin_lane_centrality` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L365 [soft] `skeletal-proof` in `theorem exists_modularGenerator_split_with_drazin_lane_centrality` — proof appears to close via minimal tactic one-liner
  - L410 [soft] `skeletal-proof` in `theorem flow_eq_unruh_modular_polynomial_of_flowEqUnruh` — proof appears to close via minimal tactic one-liner
  - L495 [soft] `law-field-locker` in `structure-field CanonicalSeedTomitaCompatibility.T` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L496 [soft] `law-field-locker` in `structure-field CanonicalSeedTomitaCompatibility.hDeltaLog` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L499 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L499 [soft] `section-law-variable` in `variable M` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L507 [soft] `skeletal-proof` in `theorem superHamiltonian_eq_tomitaGenerator` — proof appears to close via minimal tactic one-liner
  - L527 [soft] `skeletal-proof` in `theorem canonicalSeed_flow_eq_tomitaFlow` — proof appears to close via minimal tactic one-liner
  - L552 [soft] `skeletal-proof` in `theorem superHamiltonian_fixed_under_tomitaAdjointFlow` — proof appears to close via minimal tactic one-liner
  - L600 [soft] `skeletal-proof` in `theorem tomitaFlow_at_wedgeParameter` — proof appears to close via minimal tactic one-liner
  - L641 [soft] `skeletal-proof` in `theorem canonicalTomitaLogData_deltaLog` — proof appears to close via minimal tactic one-liner
  - L793 [advisory] `local-hypothesis-injection` in `theorem canonicalRelativeModularOperator_commutes_spectralProjector_of_wedgeCalibrated` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L829 [advisory] `local-hypothesis-injection` in `theorem canonicalRelativeModularOperator_mixed_blocks_zero_of_wedgeCalibrated` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L836 [advisory] `local-hypothesis-injection` in `theorem canonicalRelativeModularOperator_mixed_blocks_zero_of_wedgeCalibrated` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L991 [soft] `skeletal-proof` in `theorem canonicalSeedFlow_eq_internalUnruhFlowOfModularTime` — proof appears to close via minimal tactic one-liner
  - L1025 [soft] `skeletal-proof` in `theorem canonicalSeedFlowEqUnruhTarget_iff_superHamiltonian_exponential` — proof appears to close via minimal tactic one-liner
  - L1095 [soft] `skeletal-proof` in `theorem canonicalSeedFlowUnitCocycle_isConnesCocycle` — proof appears to close via minimal tactic one-liner
  - L1275 [soft] `skeletal-proof` in `theorem canonicalSeed_kms_relation_beta_zero_of_pairwise_commute` — proof appears to close via minimal tactic one-liner
  - L1374 [soft] `skeletal-proof` in `theorem canonicalSeedFlowEqUnruhTarget_of_superHamiltonian_identification` — proof appears to close via minimal tactic one-liner
  - L1408 [advisory] `bridge-shaped-declaration` in `theorem unruh_exponential_witness_of_modularHamiltonian_sq_one` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L1408 [soft] `skeletal-proof` in `theorem unruh_exponential_witness_of_modularHamiltonian_sq_one` — proof appears to close via minimal tactic one-liner
  - L1441 [advisory] `local-hypothesis-injection` in `theorem unruh_exponential_witness_of_modularHamiltonian_sq_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1496 [soft] `skeletal-proof` in `theorem canonicalInternalModularHamiltonian_eq_modularHamiltonian_of_bwCalibration` — proof appears to close via minimal tactic one-liner
  - L1553 [soft] `skeletal-proof` in `theorem hasDerivAt_unruhFlowOfModularTime_zero` — proof appears to close via minimal tactic one-liner
  - L1592 [advisory] `local-hypothesis-injection` in `theorem hasDerivAt_unruhFlowOfModularTime_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1632 [soft] `skeletal-proof` in `theorem superHamiltonian_eq_two_pi_modularHamiltonian_of_canonicalSeedFlowEqUnruhTarget` — proof appears to close via minimal tactic one-liner
  - L1707 [soft] `skeletal-proof` in `theorem canonicalSeedFlowEqUnruhTarget_iff_superHamiltonian_eq_two_pi_modularSign` — proof appears to close via minimal tactic one-liner
  - L1747 [soft] `skeletal-proof` in `theorem canonicalSeed_flow_at_wedgeParameter_of_flowEqUnruh` — proof appears to close via minimal tactic one-liner
  - L1825 [soft] `law-field-locker` in `structure-field CanonicalSeedUnruhCompatibility.hFlowEqUnruh` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1828 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L1828 [soft] `section-law-variable` in `variable U` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L1949 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L1949 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L2076 [soft] `skeletal-proof` in `theorem projectedEvenGenerator_fixed_under_lorentzChiralConeOrbit` — proof appears to close via minimal tactic one-liner
  - L2092 [soft] `skeletal-proof` in `theorem projectedEvenGenerator_fixed_under_lorentzWedgeOrbit` — proof appears to close via minimal tactic one-liner
  - L2125 [advisory] `existential-packaging` in `theorem exists_modularGenerator_split_with_drazin_lane_centrality_canonicalSeed` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L2144 [advisory] `existential-packaging` in `theorem exists_lorentzBivectorGenerator_split_with_drazin_lane_centrality` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L2144 [soft] `skeletal-proof` in `theorem exists_lorentzBivectorGenerator_split_with_drazin_lane_centrality` — proof appears to close via minimal tactic one-liner
  - L2175 [soft] `skeletal-proof` in `theorem supercharge_idCertifiedInverseKernel_eq_zero` — proof appears to close via minimal tactic one-liner
  - L2180 [advisory] `local-hypothesis-injection` in `theorem supercharge_idCertifiedInverseKernel_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L2202 [advisory] `local-hypothesis-injection` in `theorem superHamiltonianK_idCertifiedInverseKernel_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L2215 [advisory] `existential-packaging` in `theorem not_forall_superHamiltonian_eq_two_pi_modularHamiltonian` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

