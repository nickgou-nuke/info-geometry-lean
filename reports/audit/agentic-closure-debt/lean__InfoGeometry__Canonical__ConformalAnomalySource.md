# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:55.433293+00:00`
Root: `lean/InfoGeometry/Canonical/ConformalAnomalySource.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **61**
- Hard: **0**
- Soft: **35**
- Advisory: **26**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ConformalAnomalySource.lean` | `advisory` | 96 | 0 | 35 | 26 | 61 |

## Findings by file

### `lean/InfoGeometry/Canonical/ConformalAnomalySource.lean`
- module: `InfoGeometry.Canonical.ConformalAnomalySource`
- status: `advisory`
- debt_score: `96`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L15 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L23 [soft] `skeletal-proof` in `theorem projectorObstruction_eq_commutator` — proof appears to close via minimal tactic one-liner
  - L33 [soft] `skeletal-proof` in `theorem projectorObstruction_isGZero_of_kkt_wings` — proof appears to close via minimal tactic one-liner
  - L45 [soft] `skeletal-proof` in `theorem projectorObstruction_gOnePart_eq_zero_of_kkt_wings` — proof appears to close via minimal tactic one-liner
  - L55 [soft] `skeletal-proof` in `theorem projectorObstruction_gNegOnePart_eq_zero_of_kkt_wings` — proof appears to close via minimal tactic one-liner
  - L65 [soft] `skeletal-proof` in `theorem projectorObstruction_eq_diagonal_blocks_of_kkt_wings` — proof appears to close via minimal tactic one-liner
  - L79 [soft] `skeletal-proof` in `theorem projectorObstruction_plusProjector_mul_mul_minusProjector_eq_zero_of_kkt_wings` — proof appears to close via minimal tactic one-liner
  - L90 [soft] `skeletal-proof` in `theorem projectorObstruction_minusProjector_mul_mul_plusProjector_eq_zero_of_kkt_wings` — proof appears to close via minimal tactic one-liner
  - L141 [soft] `skeletal-proof` in `theorem obstructionScale_eq_projectorObstruction_nnnorm` — proof appears to close via minimal tactic one-liner
  - L146 [soft] `skeletal-proof` in `theorem projectorObstruction_nnnorm_eq_obstructionScale` — proof appears to close via minimal tactic one-liner
  - L151 [soft] `skeletal-proof` in `theorem chiralScale_eq_obstructionScale` — proof appears to close via minimal tactic one-liner
  - L156 [soft] `skeletal-proof` in `theorem epsilon_eq_obstructionScale` — proof appears to close via minimal tactic one-liner
  - L161 [soft] `skeletal-proof` in `theorem chiralScale_eq_projectorObstruction_norm` — proof appears to close via minimal tactic one-liner
  - L172 [soft] `skeletal-proof` in `theorem chiralScale_eq_projectorObstruction_nnnorm` — proof appears to close via minimal tactic one-liner
  - L178 [soft] `skeletal-proof` in `theorem projectorObstruction_nnnorm_eq_chiralScale` — proof appears to close via minimal tactic one-liner
  - L184 [soft] `skeletal-proof` in `theorem squashedObstructionScale_eq_tanh_obstructionScale` — proof appears to close via minimal tactic one-liner
  - L189 [soft] `simp-law-injection` in `simp-declaration projectorObstructionSquashCoeff_eq_zero_of_obstructionScale_eq_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L195 [soft] `skeletal-proof` in `theorem projectorObstructionSquashCoeff_eq_squashedObstructionScale_div_obstructionScale` — proof appears to close via minimal tactic one-liner
  - L204 [soft] `skeletal-proof` in `theorem projectorObstructionSquashCoeff_mul_obstructionScale_eq_squashedObstructionScale` — proof appears to close via minimal tactic one-liner
  - L219 [soft] `skeletal-proof` in `theorem squashedProjectorObstruction_eq_smul_projectorObstruction` — proof appears to close via minimal tactic one-liner
  - L225 [soft] `simp-law-injection` in `simp-declaration squashedProjectorObstruction_eq_zero_of_projectorObstruction_eq_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L231 [soft] `simp-law-injection` in `simp-declaration squashedProjectorObstruction_eq_zero_of_obstructionScale_eq_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L236 [advisory] `local-hypothesis-injection` in `theorem squashedProjectorObstruction_eq_smul_projectorObstruction` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L266 [advisory] `local-hypothesis-injection` in `theorem chiralScale_eq_zero_of_projectors_commute` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L271 [soft] `skeletal-proof` in `theorem chiralScale_ne_zero_of_projectors_not_commute` — proof appears to close via minimal tactic one-liner
  - L279 [advisory] `local-hypothesis-injection` in `theorem chiralScale_ne_zero_of_projectors_not_commute` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L281 [advisory] `local-hypothesis-injection` in `theorem chiralScale_ne_zero_of_projectors_not_commute` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L303 [advisory] `local-hypothesis-injection` in `theorem projectors_commute_of_anomalyDriven_normalized_fixedpoint` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L306 [advisory] `local-hypothesis-injection` in `theorem projectors_commute_of_anomalyDriven_normalized_fixedpoint` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L310 [advisory] `local-hypothesis-injection` in `theorem projectors_commute_of_anomalyDriven_normalized_fixedpoint` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L314 [advisory] `local-hypothesis-injection` in `theorem projectors_commute_of_anomalyDriven_normalized_fixedpoint` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L316 [advisory] `local-hypothesis-injection` in `theorem projectors_commute_of_anomalyDriven_normalized_fixedpoint` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L347 [advisory] `local-hypothesis-injection` in `theorem chiralScale_eq_zero_of_kahlerLogDet_unitRelativeVolume` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L348 [advisory] `local-hypothesis-injection` in `theorem chiralScale_eq_zero_of_kahlerLogDet_unitRelativeVolume` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L352 [advisory] `local-hypothesis-injection` in `theorem chiralScale_eq_zero_of_kahlerLogDet_unitRelativeVolume` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L360 [soft] `skeletal-proof` in `theorem projectors_commute_of_chiralScale_eq_zero` — proof appears to close via minimal tactic one-liner
  - L371 [advisory] `local-hypothesis-injection` in `theorem projectors_commute_of_chiralScale_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L373 [advisory] `local-hypothesis-injection` in `theorem projectors_commute_of_chiralScale_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L376 [soft] `skeletal-proof` in `theorem chiralScale_eq_zero_iff_projectors_commute` — proof appears to close via minimal tactic one-liner
  - L389 [advisory] `local-hypothesis-injection` in `theorem chiralScale_eq_zero_iff_projectors_commute` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L394 [advisory] `local-hypothesis-injection` in `theorem chiralScale_eq_zero_iff_projectors_commute` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L397 [soft] `skeletal-proof` in `theorem spectralProjector_commutator_dilation_eq_zero_of_rightProjector_commute_of_chiralScale_eq_zero` — proof appears to close via minimal tactic one-liner
  - L408 [advisory] `local-hypothesis-injection` in `theorem spectralProjector_commutator_dilation_eq_zero_of_rightProjector_commute_of_chiralScale_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L410 [advisory] `local-hypothesis-injection` in `theorem spectralProjector_commutator_dilation_eq_zero_of_rightProjector_commute_of_chiralScale_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L412 [advisory] `local-hypothesis-injection` in `theorem spectralProjector_commutator_dilation_eq_zero_of_rightProjector_commute_of_chiralScale_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L417 [soft] `skeletal-proof` in `theorem spectralProjector_commutator_dilation_eq_neg_half_projectorObstruction_of_rightProjector_commute` — proof appears to close via minimal tactic one-liner
  - L432 [soft] `skeletal-proof` in `theorem spectralProjector_commutator_dilation_eq_neg_half_projectorObstruction_of_projectorAgreement_of_metricProjector_commute` — proof appears to close via minimal tactic one-liner
  - L505 [soft] `skeletal-proof` in `theorem spectralProjector_commutator_dilation_eq_zero_of_rightProjector_commute_of_projectorObstruction_eq_zero` — proof appears to close via minimal tactic one-liner
  - L533 [soft] `skeletal-proof` in `theorem logDetBarrier_selfConcordance_mechanics_of_kahlerLogDet_unitRelativeVolume` — proof appears to close via minimal tactic one-liner
  - L548 [advisory] `local-hypothesis-injection` in `theorem logDetBarrier_selfConcordance_mechanics_of_kahlerLogDet_unitRelativeVolume` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L551 [advisory] `local-hypothesis-injection` in `theorem logDetBarrier_selfConcordance_mechanics_of_kahlerLogDet_unitRelativeVolume` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L576 [advisory] `local-hypothesis-injection` in `theorem anomalyDrivenScalarRicciFlow_of_kahlerLogDet_normalized` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L652 [soft] `skeletal-proof` in `theorem isNormalInference_iff_epsilon_eq_zero` — proof appears to close via minimal tactic one-liner
  - L657 [soft] `skeletal-proof` in `theorem isChiralInference_iff_epsilon_pos` — proof appears to close via minimal tactic one-liner
  - L714 [soft] `skeletal-proof` in `theorem unitOfAction_eq_obstructionScale` — proof appears to close via minimal tactic one-liner
  - L719 [soft] `skeletal-proof` in `theorem unitOfAction_eq_chiralScale` — proof appears to close via minimal tactic one-liner
  - L794 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L796 [soft] `skeletal-proof` in `theorem einsteinEquation_of_projectorObstruction_source` — proof appears to close via minimal tactic one-liner
  - L820 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L822 [soft] `skeletal-proof` in `theorem einsteinEquation_of_projectorObstruction_source` — proof appears to close via minimal tactic one-liner

