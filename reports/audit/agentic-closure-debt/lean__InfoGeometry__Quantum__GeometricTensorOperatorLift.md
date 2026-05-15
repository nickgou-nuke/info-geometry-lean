# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:34.539255+00:00`
Root: `lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **63**
- Hard: **0**
- Soft: **58**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean` | `advisory` | 121 | 0 | 58 | 5 | 63 |

## Findings by file

### `lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean`
- module: `InfoGeometry.Quantum.GeometricTensorOperatorLift`
- status: `advisory`
- debt_score: `121`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L20 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L22 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L50 [soft] `simp-law-injection` in `simp-declaration metricOfOperator_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L55 [soft] `simp-law-injection` in `simp-declaration metricOfOperator_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L61 [soft] `simp-law-injection` in `simp-declaration metricOfOperator_add` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L69 [soft] `simp-law-injection` in `simp-declaration metricOfOperator_neg` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L77 [soft] `simp-law-injection` in `simp-declaration metricOfOperator_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L101 [soft] `simp-law-injection` in `simp-declaration berryTwoFormJEpsOfOperator_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L110 [soft] `simp-law-injection` in `simp-declaration berryTwoFormJEpsOfOperator_apply_root` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L120 [soft] `simp-law-injection` in `simp-declaration berryTwoFormJEpsOfOperator_eq_berryOfOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L128 [soft] `simp-law-injection` in `simp-declaration berryTwoFormJEpsOfOperator_apply_eq_berryOfOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L136 [soft] `simp-law-injection` in `simp-declaration berryTwoFormJEpsOfOperator_neg` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L151 [soft] `simp-law-injection` in `simp-declaration berryOfOperator_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L159 [soft] `simp-law-injection` in `simp-declaration berryOfOperator_apply_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L167 [soft] `simp-law-injection` in `simp-declaration berryOfOperator_add` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L176 [soft] `simp-law-injection` in `simp-declaration berryOfOperator_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L183 [soft] `skeletal-proof` in `theorem berryOfOperator_modularComplexI_comp_eq_neg_metricOfOperator_of_IsPhaseLinear` — proof appears to close via minimal tactic one-liner
  - L223 [soft] `skeletal-proof` in `theorem hasDerivAt_metricOfOperator_expTransport_at_zero` — proof appears to close via minimal tactic one-liner
  - L283 [soft] `skeletal-proof` in `theorem hasDerivAt_metricOfOperator_expTransport` — proof appears to close via minimal tactic one-liner
  - L361 [soft] `skeletal-proof` in `theorem deriv_berryOfOperator_expTransport` — proof appears to close via minimal tactic one-liner
  - L384 [soft] `skeletal-proof` in `theorem deriv_metricOfOperator_modularTransport_conjugation_at_zero` — proof appears to close via minimal tactic one-liner
  - L409 [soft] `skeletal-proof` in `theorem deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_modularDeriv` — proof appears to close via minimal tactic one-liner
  - L429 [soft] `skeletal-proof` in `theorem deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_relativeModularDeriv` — proof appears to close via minimal tactic one-liner
  - L481 [soft] `skeletal-proof` in `theorem deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_modularGaugeDeriv_add_metricOf_relativeModularSourceDeriv` — proof appears to close via minimal tactic one-liner
  - L533 [soft] `skeletal-proof` in `theorem deriv_metricOfOperator_modularTransport_conjugation_at_zero_eq_metricOf_relativeModularSourceDeriv_of_commute_gaugePart` — proof appears to close via minimal tactic one-liner
  - L557 [soft] `skeletal-proof` in `theorem deriv_berryOfOperator_modularTransport_conjugation_at_zero_eq_berryOf_relativeModularDeriv` — proof appears to close via minimal tactic one-liner
  - L613 [soft] `skeletal-proof` in `theorem deriv_berryOfOperator_modularTransport_conjugation_eq_berryOfOperator_expTransport_relativeModularDeriv` — proof appears to close via minimal tactic one-liner
  - L813 [soft] `skeletal-proof` in `theorem deriv_berryOfOperator_modularTransport_conjugation_at_zero_eq_berryOf_modularGaugeDeriv_add_berryOf_relativeModularSourceDeriv` — proof appears to close via minimal tactic one-liner
  - L838 [soft] `skeletal-proof` in `theorem deriv_berryOfOperator_modularTransport_conjugation_at_zero_eq_berryOf_relativeModularSourceDeriv_of_commute_gaugePart` — proof appears to close via minimal tactic one-liner
  - L1017 [soft] `skeletal-proof` in `theorem deriv_berryOfOperator_liftedEinsteinAnomalyOperator_relativeModularTransport_at_zero_eq_berryOf_relativeModularSourceDeriv_of_commute_gaugePart` — proof appears to close via minimal tactic one-liner
  - L1161 [soft] `skeletal-proof` in `theorem deriv_metricOfOperator_starCertified_liftedEinsteinAnomalyOperator_relativeModularTransport_at_zero_eq_metricOf_relativeModularSourceDeriv_of_commute_gaugePart` — proof appears to close via minimal tactic one-liner
  - L1242 [soft] `skeletal-proof` in `theorem deriv_metricOfOperator_modularTransport_conjugation_at_zero_of_commute_relativeModularKGenerator` — proof appears to close via minimal tactic one-liner
  - L1267 [soft] `skeletal-proof` in `theorem metricOfOperator_isSymm_of_selfAdjoint` — proof appears to close via minimal tactic one-liner
  - L1282 [soft] `skeletal-proof` in `theorem metricOfOperator_K_skew_of_commutesWithK` — proof appears to close via minimal tactic one-liner
  - L1298 [advisory] `local-hypothesis-injection` in `theorem metricOfOperator_K_skew_of_commutesWithK` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1302 [soft] `skeletal-proof` in `theorem metricOfOperator_complex_i_skew_of_commutesWith_complex_i` — proof appears to close via minimal tactic one-liner
  - L1341 [soft] `skeletal-proof` in `theorem complex_i_star_eq_neg` — proof appears to close via minimal tactic one-liner
  - L1347 [soft] `skeletal-proof` in `theorem isSelfAdjoint_modularComplexI_comp_of_star_eq_neg_of_commutesWithK` — proof appears to close via minimal tactic one-liner
  - L1361 [advisory] `local-hypothesis-injection` in `theorem isSelfAdjoint_modularComplexI_comp_of_star_eq_neg_of_commutesWithK` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1378 [soft] `skeletal-proof` in `theorem isPhaseLinear_modularComplexI_comp_of_IsPhaseLinear` — proof appears to close via minimal tactic one-liner
  - L1416 [soft] `simp-law-injection` in `simp-declaration berryOfOperator_eq_qgtOfOperator_berry` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1445 [soft] `simp-law-injection` in `simp-declaration qgtOfSkewPhaseLinearOperator_berry_eq_berryOfOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1465 [soft] `simp-law-injection` in `simp-declaration qgtOfSkewPhaseLinearOperator_berry_eq_neg_metricOfOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1519 [soft] `simp-law-injection` in `simp-declaration starCertifiedEinsteinAnomalyQGT_berry_eq_berryOfOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1536 [soft] `skeletal-proof` in `theorem starCertifiedEinsteinAnomalyQGT_berry_eq_metricOfOperator_liftedProjectorObstructionOperator_of_projectorAgreement` — proof appears to close via minimal tactic one-liner
  - L1588 [soft] `simp-law-injection` in `simp-declaration kreinMetricOfOperator_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1603 [soft] `skeletal-proof` in `theorem kreinMetricOfOperator_K_skew_of_IsPhaseAntilinear` — proof appears to close via minimal tactic one-liner
  - L1645 [soft] `skeletal-proof` in `theorem metricOfOperator_spectral_epsilon_comp_eq_kreinMetricOfOperator` — proof appears to close via minimal tactic one-liner
  - L1654 [soft] `simp-law-injection` in `simp-declaration inner_modularSignEpsilon_apply_eq_kreinInner` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1662 [soft] `simp-law-injection` in `simp-declaration inner_spectral_epsilon_apply_eq_kreinInner` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1671 [soft] `simp-law-injection` in `simp-declaration inner_apply_modularSignEpsilon_eq_kreinInner` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1685 [soft] `simp-law-injection` in `simp-declaration inner_apply_spectral_epsilon_eq_kreinInner` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1708 [soft] `skeletal-proof` in `theorem modularVarianceSeed_eq_spectral_epsilon_comp` — proof appears to close via minimal tactic one-liner
  - L1718 [soft] `skeletal-proof` in `theorem metricOfOperator_modularVarianceSeed_diag_eq_modularVariance` — proof appears to close via minimal tactic one-liner
  - L1760 [soft] `skeletal-proof` in `theorem isSelfAdjoint_modularSignEpsilon_comp_of_kreinSelfAdjoint` — proof appears to close via minimal tactic one-liner
  - L1781 [soft] `skeletal-proof` in `theorem isSelfAdjoint_spectral_epsilon_comp_of_kreinSelfAdjoint` — proof appears to close via minimal tactic one-liner
  - L1789 [soft] `skeletal-proof` in `theorem isPhaseLinear_modularSignEpsilon_comp_of_IsPhaseAntilinear` — proof appears to close via minimal tactic one-liner
  - L1831 [soft] `skeletal-proof` in `theorem isPhaseLinear_spectral_epsilon_comp_of_IsPhaseAntilinear` — proof appears to close via minimal tactic one-liner
  - L1853 [soft] `skeletal-proof` in `theorem qgtOfOperator_modularSignEpsilon_comp_metric_eq_kreinQgtOfOperator_metric` — proof appears to close via minimal tactic one-liner
  - L1874 [soft] `skeletal-proof` in `theorem qgtOfOperator_spectral_epsilon_comp_metric_eq_kreinQgtOfOperator_metric` — proof appears to close via minimal tactic one-liner
  - L1892 [soft] `skeletal-proof` in `theorem qgtOfOperator_modularSignEpsilon_comp_berry_eq_kreinQgtOfOperator_berry` — proof appears to close via minimal tactic one-liner
  - L1913 [soft] `skeletal-proof` in `theorem qgtOfOperator_spectral_epsilon_comp_berry_eq_kreinQgtOfOperator_berry` — proof appears to close via minimal tactic one-liner

