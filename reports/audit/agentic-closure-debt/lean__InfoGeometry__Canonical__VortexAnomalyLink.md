# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:09.769669+00:00`
Root: `lean/InfoGeometry/Canonical/VortexAnomalyLink.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **66**
- Hard: **0**
- Soft: **41**
- Advisory: **25**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/VortexAnomalyLink.lean` | `advisory` | 107 | 0 | 41 | 25 | 66 |

## Findings by file

### `lean/InfoGeometry/Canonical/VortexAnomalyLink.lean`
- module: `InfoGeometry.Canonical.VortexAnomalyLink`
- status: `advisory`
- debt_score: `107`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L47 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L49 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L50 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L51 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L63 [soft] `law-field-locker` in `structure-field VortexPair.source_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L64 [soft] `law-field-locker` in `structure-field VortexPair.sink_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L65 [soft] `law-field-locker` in `structure-field VortexPair.source_sink_orth` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L66 [soft] `law-field-locker` in `structure-field VortexPair.sink_source_orth` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [soft] `law-field-locker` in `structure-field VortexPair.sum_id` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [soft] `law-field-locker` in `structure-field VortexPair.source_comm_eps` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L71 [soft] `law-field-locker` in `structure-field VortexPair.sink_comm_eps` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L74 [soft] `law-field-locker` in `structure-field VortexPair.source_comp_J` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L77 [soft] `law-field-locker` in `structure-field VortexPair.sink_comp_J` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L99 [soft] `skeletal-proof` in `theorem canonicalVortexPair_source_comm_spectral_epsilon` — proof appears to close via minimal tactic one-liner
  - L107 [soft] `skeletal-proof` in `theorem canonicalVortexPair_sink_comm_spectral_epsilon` — proof appears to close via minimal tactic one-liner
  - L115 [soft] `skeletal-proof` in `theorem canonicalVortexPair_source_comp_modular_j` — proof appears to close via minimal tactic one-liner
  - L123 [soft] `skeletal-proof` in `theorem canonicalVortexPair_sink_comp_modular_j` — proof appears to close via minimal tactic one-liner
  - L146 [soft] `simp-law-injection` in `simp-declaration canonicalSourceBoundarySupercharge_eq_left` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L153 [soft] `simp-law-injection` in `simp-declaration canonicalSinkBoundarySupercharge_eq_right` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L160 [soft] `simp-law-injection` in `simp-declaration canonicalSourceBoundarySupercharge_sq_eq_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L169 [soft] `simp-law-injection` in `simp-declaration canonicalSinkBoundarySupercharge_sq_eq_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L204 [soft] `simp-law-injection` in `simp-declaration sourceVortexSeed_eq_neg_plusProjectorFlux` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L217 [soft] `simp-law-injection` in `simp-declaration sinkVortexSeed_eq_neg_minusProjectorFlux` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L230 [soft] `simp-law-injection` in `simp-declaration sourceVortexSeed_add_sinkVortexSeed_eq_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L233 [soft] `skeletal-proof` in `theorem sourceVortexSeed_add_sinkVortexSeed_eq_zero` — proof appears to close via minimal tactic one-liner
  - L250 [soft] `simp-law-injection` in `simp-declaration sourceVortexSeed_eq_neg_sinkVortexSeed` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L259 [soft] `simp-law-injection` in `simp-declaration sourceSinkAnticommutator_sum_eq_two_smul_connectionGenerator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L265 [soft] `skeletal-proof` in `theorem sourceSinkAnticommutator_sum_eq_two_smul_connectionGenerator` — proof appears to close via minimal tactic one-liner
  - L297 [soft] `simp-law-injection` in `simp-declaration canonicalVortexPair_source_sub_sink_eq_spectral_epsilon` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L300 [soft] `skeletal-proof` in `theorem canonicalVortexPair_source_sub_sink_eq_spectral_epsilon` — proof appears to close via minimal tactic one-liner
  - L329 [soft] `simp-law-injection` in `simp-declaration sourceVortexSeed_sub_sinkVortexSeed_eq_transportCommutator_spectral_epsilon` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L336 [soft] `skeletal-proof` in `theorem sourceVortexSeed_sub_sinkVortexSeed_eq_transportCommutator_spectral_epsilon` — proof appears to close via minimal tactic one-liner
  - L359 [soft] `simp-law-injection` in `simp-declaration sourceSinkAnticommutator_sub_eq_anticommutator_spectral_epsilon` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L409 [soft] `simp-law-injection` in `simp-declaration transportCommutator_spectral_epsilon_eq_two_smul_sourceVortexSeed` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L415 [soft] `skeletal-proof` in `theorem transportCommutator_spectral_epsilon_eq_two_smul_sourceVortexSeed` — proof appears to close via minimal tactic one-liner
  - L421 [advisory] `local-hypothesis-injection` in `theorem transportCommutator_spectral_epsilon_eq_two_smul_sourceVortexSeed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L423 [advisory] `local-hypothesis-injection` in `theorem transportCommutator_spectral_epsilon_eq_two_smul_sourceVortexSeed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L436 [soft] `simp-law-injection` in `simp-declaration transportCommutator_spectral_epsilon_eq_neg_two_smul_sinkVortexSeed` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L442 [soft] `skeletal-proof` in `theorem transportCommutator_spectral_epsilon_eq_neg_two_smul_sinkVortexSeed` — proof appears to close via minimal tactic one-liner
  - L454 [soft] `simp-law-injection` in `simp-declaration sourceVortexSeed_eq_half_transportCommutator_spectral_epsilon` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L460 [soft] `skeletal-proof` in `theorem sourceVortexSeed_eq_half_transportCommutator_spectral_epsilon` — proof appears to close via minimal tactic one-liner
  - L472 [soft] `simp-law-injection` in `simp-declaration sinkVortexSeed_eq_neg_half_transportCommutator_spectral_epsilon` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L478 [soft] `skeletal-proof` in `theorem sinkVortexSeed_eq_neg_half_transportCommutator_spectral_epsilon` — proof appears to close via minimal tactic one-liner
  - L534 [soft] `simp-law-injection` in `simp-declaration sourceAnticommutator_eq_connectionGenerator_add_half_anticommutator_spectral_epsilon` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L560 [advisory] `local-hypothesis-injection` in `theorem sourceAnticommutator_eq_connectionGenerator_add_half_anticommutator_spectral_epsilon` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L570 [advisory] `local-hypothesis-injection` in `theorem sourceAnticommutator_eq_connectionGenerator_add_half_anticommutator_spectral_epsilon` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L599 [soft] `simp-law-injection` in `simp-declaration sinkAnticommutator_eq_connectionGenerator_sub_half_anticommutator_spectral_epsilon` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L625 [advisory] `local-hypothesis-injection` in `theorem sinkAnticommutator_eq_connectionGenerator_sub_half_anticommutator_spectral_epsilon` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L628 [advisory] `local-hypothesis-injection` in `theorem sinkAnticommutator_eq_connectionGenerator_sub_half_anticommutator_spectral_epsilon` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L655 [soft] `skeletal-proof` in `theorem sourceVortexSeed_comp_J_eq_J_comp_sinkVortexSeed_of_commute_modularJ` — proof appears to close via minimal tactic one-liner
  - L665 [advisory] `local-hypothesis-injection` in `theorem sourceVortexSeed_comp_J_eq_J_comp_sinkVortexSeed_of_commute_modularJ` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L667 [advisory] `local-hypothesis-injection` in `theorem sourceVortexSeed_comp_J_eq_J_comp_sinkVortexSeed_of_commute_modularJ` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L692 [soft] `skeletal-proof` in `theorem sinkVortexSeed_comp_J_eq_J_comp_sourceVortexSeed_of_commute_modularJ` — proof appears to close via minimal tactic one-liner
  - L702 [advisory] `local-hypothesis-injection` in `theorem sinkVortexSeed_comp_J_eq_J_comp_sourceVortexSeed_of_commute_modularJ` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L704 [advisory] `local-hypothesis-injection` in `theorem sinkVortexSeed_comp_J_eq_J_comp_sourceVortexSeed_of_commute_modularJ` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L740 [advisory] `existential-packaging` in `theorem exists_sourceSinkSeedLocalizedVortex_of_operatorialCentralCharge_ne_zero_of_boundaryGenerator_eq_source_of_identifiedTransportedPolarization` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L790 [advisory] `existential-packaging` in `theorem exists_sourceSinkSeedLocalizedVortex_of_operatorialCentralChargeParity_ne_zero_of_boundaryGenerator_eq_source_of_identifiedTransportedPolarization` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L830 [advisory] `existential-packaging` in `theorem exists_sourceSinkSeedLocalizedVortex_of_operatorialCentralCharge_ne_zero_of_boundaryGenerator_eq_sink_of_identifiedTransportedPolarization` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L880 [advisory] `existential-packaging` in `theorem exists_sourceSinkSeedLocalizedVortex_of_operatorialCentralChargeParity_ne_zero_of_boundaryGenerator_eq_sink_of_identifiedTransportedPolarization` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L918 [advisory] `existential-packaging` in `theorem exists_sourceSinkSeedLocalizedVortex_of_operatorialCentralCharge_ne_zero_of_kernelSeparation_of_boundaryGenerator_eq_source_of_identifiedTransportedPolarization` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L946 [advisory] `local-hypothesis-injection` in `theorem exists_sourceSinkSeedLocalizedVortex_of_operatorialCentralCharge_ne_zero_of_kernelSeparation_of_boundaryGenerator_eq_source_of_identifiedTransportedPolarization` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L957 [advisory] `existential-packaging` in `theorem exists_sourceSinkSeedLocalizedVortex_of_operatorialCentralChargeParity_ne_zero_of_kernelSeparation_of_boundaryGenerator_eq_source_of_identifiedTransportedPolarization` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L994 [advisory] `existential-packaging` in `theorem exists_sourceSinkSeedLocalizedVortex_of_operatorialCentralCharge_ne_zero_of_kernelSeparation_of_boundaryGenerator_eq_sink_of_identifiedTransportedPolarization` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1022 [advisory] `local-hypothesis-injection` in `theorem exists_sourceSinkSeedLocalizedVortex_of_operatorialCentralCharge_ne_zero_of_kernelSeparation_of_boundaryGenerator_eq_sink_of_identifiedTransportedPolarization` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1033 [advisory] `existential-packaging` in `theorem exists_sourceSinkSeedLocalizedVortex_of_operatorialCentralChargeParity_ne_zero_of_kernelSeparation_of_boundaryGenerator_eq_sink_of_identifiedTransportedPolarization` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

