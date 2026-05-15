# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:34.957213+00:00`
Root: `lean/InfoGeometry/Quantum/HestenesKahler.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **43**
- Hard: **0**
- Soft: **35**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Quantum/HestenesKahler.lean` | `advisory` | 78 | 0 | 35 | 8 | 43 |

## Findings by file

### `lean/InfoGeometry/Quantum/HestenesKahler.lean`
- module: `InfoGeometry.Quantum.HestenesKahler`
- status: `advisory`
- debt_score: `78`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L53 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L55 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L79 [soft] `law-field-locker` in `structure-field PhaseGradedOperator.hasParity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L100 [soft] `law-field-locker` in `structure-field BigradedOperator.hasPhaseParity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L120 [soft] `law-field-locker` in `structure-field ProjectivePolarizedBigradedBogoliubovDatum.representative` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L122 [soft] `law-field-locker` in `structure-field ProjectivePolarizedBigradedBogoliubovDatum.majorana` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L123 [soft] `law-field-locker` in `structure-field ProjectivePolarizedBigradedBogoliubovDatum.polarization` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L124 [soft] `law-field-locker` in `structure-field ProjectivePolarizedBigradedBogoliubovDatum.J_eq_modularConjugationJ` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L126 [soft] `law-field-locker` in `structure-field ProjectivePolarizedBigradedBogoliubovDatum.eps_eq_modularSignEpsilon` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L177 [soft] `skeletal-proof` in `theorem ray_eq_of_smul_representative` — proof appears to close via minimal tactic one-liner
  - L197 [soft] `skeletal-proof` in `theorem K_eq_modularComplexI` — proof appears to close via minimal tactic one-liner
  - L204 [soft] `skeletal-proof` in `theorem J_eq_modular_j` — proof appears to close via minimal tactic one-liner
  - L211 [soft] `skeletal-proof` in `theorem eps_eq_spectral_epsilon` — proof appears to close via minimal tactic one-liner
  - L218 [advisory] `bridge-shaped-declaration` in `theorem compat` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L226 [advisory] `bridge-shaped-declaration` in `theorem compat_complex_i` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L235 [soft] `skeletal-proof` in `theorem K_maps_plus_to_minus` — proof appears to close via minimal tactic one-liner
  - L243 [soft] `skeletal-proof` in `theorem K_maps_minus_to_plus` — proof appears to close via minimal tactic one-liner
  - L251 [soft] `skeletal-proof` in `theorem aPlus_sub_aMinus_eq_polarization` — proof appears to close via minimal tactic one-liner
  - L258 [soft] `skeletal-proof` in `theorem isProjectorSuperPair_aMinus_aPlus` — proof appears to close via minimal tactic one-liner
  - L277 [soft] `skeletal-proof` in `theorem eps_phase_odd` — proof appears to close via minimal tactic one-liner
  - L383 [soft] `simp-law-injection` in `simp-declaration certifiedProjectorObstructionAxis_bidegree` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L389 [soft] `skeletal-proof` in `lemma comp_modularComplexI_isPhaseAntilinear` — proof appears to close via minimal tactic one-liner
  - L399 [advisory] `local-hypothesis-injection` in `lemma comp_modularComplexI_isPhaseAntilinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L409 [advisory] `local-hypothesis-injection` in `lemma comp_modularComplexI_isPhaseAntilinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L416 [soft] `skeletal-proof` in `lemma comp_complex_i_isPhaseAntilinear` — proof appears to close via minimal tactic one-liner
  - L448 [soft] `simp-law-injection` in `simp-declaration weldedProjectorObstructionAxis_bidegree` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L467 [advisory] `local-hypothesis-injection` in `theorem weldedProjectorObstructionAxis_eq_zero_of_operatorialIncidence` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L541 [soft] `skeletal-proof` in `theorem weldedProjectorObstruction_state_split` — proof appears to close via minimal tactic one-liner
  - L564 [soft] `skeletal-proof` in `theorem weldedProjectorObstruction_pairedSourceCancellation` — proof appears to close via minimal tactic one-liner
  - L594 [soft] `simp-law-injection` in `simp-declaration starCertifiedEinsteinAnomalyAxis_bidegree` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L642 [soft] `simp-law-injection` in `simp-declaration certifiedProjectorObstructionStateInducedDynamics_eq_relativeModularDeriv` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L650 [soft] `simp-law-injection` in `simp-declaration starCertifiedEinsteinAnomalyStateInducedDynamics_eq_relativeModularDeriv` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L658 [soft] `simp-law-injection` in `simp-declaration certifiedProjectorObstructionStateMetricReadout_eq_hestenesMetricTwoForm` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L666 [soft] `simp-law-injection` in `simp-declaration certifiedProjectorObstructionStatePhaseReadout_eq_hestenesBerryTwoForm` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L674 [soft] `simp-law-injection` in `simp-declaration certifiedProjectorObstructionStatePhaseReadout_eq_metric_comp_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L697 [soft] `simp-law-injection` in `simp-declaration certifiedProjectorObstructionStatePhaseReadout_eq_metric_comp_K` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L713 [soft] `simp-law-injection` in `simp-declaration starCertifiedEinsteinAnomalyStateMetricReadout_eq_hestenesMetricTwoForm` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L721 [soft] `simp-law-injection` in `simp-declaration starCertifiedEinsteinAnomalyStatePhaseReadout_eq_hestenesBerryTwoForm` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L729 [soft] `simp-law-injection` in `simp-declaration starCertifiedEinsteinAnomalyStatePhaseReadout_eq_metric_comp_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L752 [soft] `simp-law-injection` in `simp-declaration starCertifiedEinsteinAnomalyStatePhaseReadout_eq_metric_comp_K` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L804 [soft] `skeletal-proof` in `theorem starCertifiedEinsteinAnomalyStatePhaseReadout_eq_projectorObstructionMetric_of_projectorAgreement` — proof appears to close via minimal tactic one-liner
  - L817 [soft] `skeletal-proof` in `theorem weldedProjectorObstructionStatePhaseReadout_eq_projectorObstructionMetric_of_projectorAgreement` — proof appears to close via minimal tactic one-liner

