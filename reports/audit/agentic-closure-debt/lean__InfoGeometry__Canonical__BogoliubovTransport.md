# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:44.156291+00:00`
Root: `lean/InfoGeometry/Canonical/BogoliubovTransport.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **48**
- Hard: **0**
- Soft: **41**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/BogoliubovTransport.lean` | `advisory` | 89 | 0 | 41 | 7 | 48 |

## Findings by file

### `lean/InfoGeometry/Canonical/BogoliubovTransport.lean`
- module: `InfoGeometry.Canonical.BogoliubovTransport`
- status: `advisory`
- debt_score: `89`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L33 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L35 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L36 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L53 [soft] `skeletal-proof` in `theorem isPhaseLinear_iff_comp_complex_i` — proof appears to close via minimal tactic one-liner
  - L65 [soft] `skeletal-proof` in `theorem isPhaseAntilinear_iff_comp_complex_i` — proof appears to close via minimal tactic one-liner
  - L85 [soft] `simp-law-injection` in `simp-declaration phaseLinearPart_add_phaseAntilinearPart` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L112 [advisory] `local-hypothesis-injection` in `lemma phaseConjugate_comp_phaseAxis` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L127 [advisory] `local-hypothesis-injection` in `lemma phaseAxis_comp_phaseConjugate` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L133 [soft] `skeletal-proof` in `lemma neg_phaseConjugate_comp_phaseAxis` — proof appears to close via minimal tactic one-liner
  - L139 [soft] `skeletal-proof` in `lemma neg_phaseAxis_comp_phaseConjugate` — proof appears to close via minimal tactic one-liner
  - L145 [soft] `skeletal-proof` in `theorem phaseLinearPart_isPhaseLinear` — proof appears to close via minimal tactic one-liner
  - L167 [soft] `skeletal-proof` in `theorem phaseAntilinearPart_isPhaseAntilinear` — proof appears to close via minimal tactic one-liner
  - L231 [soft] `skeletal-proof` in `theorem phaseLinearPart_eq_self_of_IsPhaseLinear` — proof appears to close via minimal tactic one-liner
  - L244 [soft] `skeletal-proof` in `theorem phaseAntilinearPart_eq_self_of_IsPhaseAntilinear` — proof appears to close via minimal tactic one-liner
  - L299 [soft] `skeletal-proof` in `lemma lieBracket_eq_transportCommutator` — proof appears to close via minimal tactic one-liner
  - L366 [soft] `skeletal-proof` in `theorem transportCommutator_split_generator` — proof appears to close via minimal tactic one-liner
  - L436 [soft] `skeletal-proof` in `theorem phaseAxisForce_eq_from_phaseAntilinearPart` — proof appears to close via minimal tactic one-liner
  - L499 [soft] `simp-law-injection` in `simp-declaration JBoost_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L504 [soft] `simp-law-injection` in `simp-declaration epsilonBoost_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L509 [soft] `simp-law-injection` in `simp-declaration KRotation_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L512 [soft] `skeletal-proof` in `theorem JBoost_add` — proof appears to close via minimal tactic one-liner
  - L526 [soft] `skeletal-proof` in `theorem epsilonBoost_add` — proof appears to close via minimal tactic one-liner
  - L540 [soft] `skeletal-proof` in `theorem KRotation_add` — proof appears to close via minimal tactic one-liner
  - L718 [soft] `skeletal-proof` in `theorem relativeModularDeriv_eq_zero_of_commute_generator` — proof appears to close via minimal tactic one-liner
  - L762 [soft] `skeletal-proof` in `theorem commute_clockAxis_of_IsPhaseLinear` — proof appears to close via minimal tactic one-liner
  - L772 [soft] `skeletal-proof` in `theorem modularTransportGenerator_isPhaseLinear_of_scalePart_eq_zero` — proof appears to close via minimal tactic one-liner
  - L780 [advisory] `local-hypothesis-injection` in `theorem modularTransportGenerator_isPhaseLinear_of_scalePart_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L942 [soft] `skeletal-proof` in `theorem deriv_modularTransport_conjugation_eq_expTransport_modularDeriv` — proof appears to close via minimal tactic one-liner
  - L1006 [soft] `skeletal-proof` in `theorem deriv_modularTransport_conjugation_eq_expTransport_potentialPreserving_add_expTransport_potentialChanging` — proof appears to close via minimal tactic one-liner
  - L1047 [soft] `skeletal-proof` in `theorem deriv_modularTransport_conjugation_eq_expTransport_potentialChanging_of_commute_potentialPreserving` — proof appears to close via minimal tactic one-liner
  - L1080 [soft] `simp-law-injection` in `simp-declaration modularTransportFlow_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1095 [soft] `skeletal-proof` in `theorem modularTransportGenerator_mem_skewAdjoint_of_isSelfAdjoint_of_IsPhaseLinear` — proof appears to close via minimal tactic one-liner
  - L1137 [soft] `skeletal-proof` in `theorem modularComplexI_commutes_modularTransportGenerator_of_IsPhaseLinear` — proof appears to close via minimal tactic one-liner
  - L1162 [soft] `skeletal-proof` in `theorem complex_i_commutes_modularTransportGenerator_of_IsPhaseLinear` — proof appears to close via minimal tactic one-liner
  - L1168 [soft] `skeletal-proof` in `theorem modularTransportFlow_preserves_inner_of_isSelfAdjoint_of_IsPhaseLinear` — proof appears to close via minimal tactic one-liner
  - L1205 [soft] `simp-law-injection` in `simp-declaration inner_modularSignEpsilon_apply_eq_kreinInner` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1215 [soft] `skeletal-proof` in `theorem modularSignEpsilon_comp_modularTransportFlow_eq_modularTransportFlow_comp_modularSignEpsilon_of_commute_generator` — proof appears to close via minimal tactic one-liner
  - L1278 [soft] `skeletal-proof` in `theorem modularComplexI_comp_modularTransportFlow_eq_modularTransportFlow_comp_modularComplexI_of_IsPhaseLinear` — proof appears to close via minimal tactic one-liner
  - L1295 [soft] `skeletal-proof` in `theorem complex_i_comp_modularTransportFlow_eq_modularTransportFlow_comp_complex_i_of_IsPhaseLinear` — proof appears to close via minimal tactic one-liner
  - L1307 [soft] `skeletal-proof` in `theorem modularTransportFlow_eq_KRotation_of_generator_eq_smul_phaseAxis` — proof appears to close via minimal tactic one-liner
  - L1328 [soft] `skeletal-proof` in `theorem modularTransportFlow_eq_KRotation_of_generator_eq_smul_complex_i` — proof appears to close via minimal tactic one-liner
  - L1361 [soft] `simp-law-injection` in `simp-declaration kreinExpectation_add` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1367 [soft] `simp-law-injection` in `simp-declaration kreinExpectation_neg` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1373 [soft] `simp-law-injection` in `simp-declaration kreinExpectation_sub` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1379 [soft] `simp-law-injection` in `simp-declaration kreinExpectation_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1385 [soft] `simp-law-injection` in `simp-declaration kreinExpectation_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1436 [soft] `skeletal-proof` in `theorem modularVariance_nonneg_iff_signed_secondMoment_nonneg` — proof appears to close via minimal tactic one-liner

