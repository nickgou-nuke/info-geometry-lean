# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:52.241661+00:00`
Root: `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **63**
- Hard: **0**
- Soft: **55**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean` | `advisory` | 118 | 0 | 55 | 8 | 63 |

## Findings by file

### `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean`
- module: `InfoGeometry.Canonical.RelativePotentialCountBridge`
- status: `advisory`
- debt_score: `118`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L31 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L68 [soft] `simp-law-injection` in `simp-declaration relativeCountDensity_common_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L77 [soft] `simp-law-injection` in `simp-declaration rawCountDelta_common_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L85 [soft] `simp-law-injection` in `simp-declaration relativeCountLogDensity_common_pos_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L93 [soft] `simp-law-injection` in `simp-declaration relativeCountModularProfile_common_pos_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L128 [soft] `simp-law-injection` in `simp-declaration doubledAtomEpsilonOp_eq_spectralEpsilon` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L144 [soft] `simp-law-injection` in `simp-declaration averagedKreinTomitaTakesakiOp_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L163 [soft] `simp-law-injection` in `simp-declaration averagedTomitaTakesakiOp_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L173 [soft] `simp-law-injection` in `simp-declaration averagedRawCountHamiltonian_common_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L181 [soft] `simp-law-injection` in `simp-declaration averagedRawCountHamiltonian_eq_mean_rawCountHamiltonianProfile` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L202 [soft] `simp-law-injection` in `simp-declaration averagedRawCountKreinTomitaTakesakiOp_common_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L210 [soft] `simp-law-injection` in `simp-declaration averagedRawCountKreinTomitaTakesakiOp_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L222 [soft] `simp-law-injection` in `simp-declaration averagedRawCountTomitaTakesakiOp_common_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L230 [soft] `simp-law-injection` in `simp-declaration averagedRawCountTomitaTakesakiOp_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L249 [soft] `simp-law-injection` in `simp-declaration relativeKreinTomitaTakesakiOp_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L262 [soft] `simp-law-injection` in `simp-declaration relativeTomitaTakesakiOp_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L287 [advisory] `existential-packaging` in `theorem rawCountDelta_cocycle` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L297 [soft] `simp-law-injection` in `simp-declaration relativeCountLogDensity_cocycle` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L348 [advisory] `existential-packaging` in `def countMassShift` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L355 [soft] `simp-law-injection` in `simp-declaration countMassShift_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L364 [soft] `simp-law-injection` in `simp-declaration countMassShift_symm` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L375 [soft] `simp-law-injection` in `simp-declaration countMassShift_cocycle` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L392 [soft] `simp-law-injection` in `simp-declaration representativeRelativeDensity_positiveMeasureOfCounts_eq_relativeCountDensity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L404 [soft] `simp-law-injection` in `simp-declaration representativeRelativeLogDensity_positiveMeasureOfCounts_eq_relativeCountLogDensity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L416 [soft] `simp-law-injection` in `simp-declaration representativeModularPotential_positiveMeasureOfCounts_eq_relativeCountModularProfile` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L428 [soft] `simp-law-injection` in `simp-declaration relativeCountDensity_eq_exp_relativeCountLogDensity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L438 [soft] `simp-law-injection` in `simp-declaration relativeCountDensity_eq_exp_neg_relativeCountModularProfile` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L454 [soft] `simp-law-injection` in `simp-declaration gaugeSection_countRay_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L463 [soft] `simp-law-injection` in `simp-declaration gaugeSectionFinProb_countRay_apply_toReal` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L465 [soft] `skeletal-proof` in `theorem gaugeSectionFinProb_countRay_apply_toReal` — proof appears to close via minimal tactic one-liner
  - L475 [soft] `simp-law-injection` in `simp-declaration relativeDensity_countRay_eq_massRatio_mul_relativeCountDensity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L491 [soft] `simp-law-injection` in `simp-declaration relativeLogDensity_countRay_eq_relativeCountLogDensity_add_massShift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L509 [soft] `simp-law-injection` in `simp-declaration relativeModularPotential_countRay_eq_neg_relativeCountLogDensity_sub_massShift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L534 [advisory] `existential-packaging` in `lemma countRelativeVolumeChange_pos` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L542 [soft] `simp-law-injection` in `simp-declaration countMassShift_eq_neg_log_countRelativeVolumeChange` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L557 [soft] `simp-law-injection` in `simp-declaration countMassShift_eq_scalarModularPotential_relativeVolumeChange` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L568 [soft] `simp-law-injection` in `simp-declaration exp_neg_countMassShift_eq_countRelativeVolumeChange` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L579 [soft] `simp-law-injection` in `simp-declaration relativeDensity_countRay_eq_relativeCountDensity_div_countRelativeVolumeChange` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L597 [soft] `simp-law-injection` in `simp-declaration relativeLogDensity_countRay_eq_relativeCountLogDensity_sub_log_countRelativeVolumeChange` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L643 [soft] `simp-law-injection` in `simp-declaration projectiveCountHamiltonianProfile_eq_relativeModularPotential_countRay` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L645 [soft] `skeletal-proof` in `theorem projectiveCountHamiltonianProfile_eq_relativeModularPotential_countRay` — proof appears to close via minimal tactic one-liner
  - L655 [soft] `simp-law-injection` in `simp-declaration projectiveCountLogDelta_eq_relativeLogDensity_countRay` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L662 [soft] `simp-law-injection` in `simp-declaration projectiveCountModularProfile_eq_neg_relativeLogDensity_countRay` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L673 [soft] `simp-law-injection` in `simp-declaration projectiveCountDelta_eq_massRatio_mul_rawCountDelta` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L686 [soft] `simp-law-injection` in `simp-declaration projectiveCountDelta_eq_raw_div_countRelativeVolumeChange` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L698 [soft] `simp-law-injection` in `simp-declaration projectiveCountLogDelta_eq_rawCountLogDelta_add_massShift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L710 [soft] `simp-law-injection` in `simp-declaration projectiveCountModularProfile_eq_neg_log_projectiveCountDelta` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L722 [soft] `simp-law-injection` in `simp-declaration projectiveCountDelta_eq_exp_neg_projectiveCountModularProfile` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L737 [soft] `simp-law-injection` in `simp-declaration projectiveCountHamiltonianProfile_eq_rawCountHamiltonianProfile_sub_massShift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L751 [advisory] `existential-packaging` in `def averagedProjectiveCountHamiltonian` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L758 [soft] `simp-law-injection` in `simp-declaration averagedProjectiveCountHamiltonian_eq_mean_projectiveCountHamiltonianProfile` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L780 [soft] `simp-law-injection` in `simp-declaration averagedProjectiveCountHamiltonian_eq_averagedRawCountHamiltonian_sub_massShift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L799 [advisory] `local-hypothesis-injection` in `def averagedProjectiveCountHamiltonian` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L801 [advisory] `local-hypothesis-injection` in `def averagedProjectiveCountHamiltonian` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L814 [soft] `simp-law-injection` in `simp-declaration averagedProjectiveCountKreinTomitaTakesakiOp_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L837 [soft] `simp-law-injection` in `simp-declaration projectiveCountModularProfile_eq_raw_sub_scalarModularPotential_relativeVolumeChange` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L859 [soft] `simp-law-injection` in `simp-declaration relativeModularPotential_countRay_eq_relativeCountModularProfile_sub_scalarModularPotential_relativeVolumeChange` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L873 [soft] `simp-law-injection` in `simp-declaration projectiveCountDelta_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L881 [soft] `simp-law-injection` in `simp-declaration projectiveCountLogDelta_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L889 [soft] `simp-law-injection` in `simp-declaration projectiveCountHamiltonianProfile_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L946 [soft] `simp-law-injection` in `simp-declaration projectiveLogGenerator_countRay_eq_neg_relativeCountLogDensity_sub_massShift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L967 [soft] `simp-law-injection` in `simp-declaration projectiveLogGenerator_countRay_eq_projectiveCountHamiltonianProfile` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

