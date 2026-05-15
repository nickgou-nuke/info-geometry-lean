# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:55.699210+00:00`
Root: `lean/InfoGeometry/Canonical/ConformalProjectorCore.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **50**
- Hard: **0**
- Soft: **31**
- Advisory: **19**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ConformalProjectorCore.lean` | `advisory` | 81 | 0 | 31 | 19 | 50 |

## Findings by file

### `lean/InfoGeometry/Canonical/ConformalProjectorCore.lean`
- module: `InfoGeometry.Canonical.ConformalProjectorCore`
- status: `advisory`
- debt_score: `81`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L52 [soft] `law-field-locker` in `structure-field StarCertifiedConformalInference.spectralProjector_star` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L63 [soft] `law-field-locker` in `structure-field ProjectorAgreementCertifiedConformalInference.projectorAgreement` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L87 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L96 [soft] `simp-law-injection` in `simp-declaration toCertifiedConformalInference_toCertifiedInverseKernel` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L133 [soft] `simp-law-injection` in `simp-declaration projectorObstructionOperator_eq_leftChiralAnomalyOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L136 [soft] `simp-law-injection` in `simp-declaration projectorObstructionOperator_eq_chiralAnomalyOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L146 [soft] `skeletal-proof` in `theorem spectralProjector_idempotent` — proof appears to close via minimal tactic one-liner
  - L152 [soft] `skeletal-proof` in `theorem mpRangeProjector_idempotent` — proof appears to close via minimal tactic one-liner
  - L158 [soft] `skeletal-proof` in `theorem metricProjector_idempotent` — proof appears to close via minimal tactic one-liner
  - L164 [soft] `skeletal-proof` in `theorem metricProjector_star` — proof appears to close via minimal tactic one-liner
  - L170 [soft] `skeletal-proof` in `theorem mpRangeProjector_star` — proof appears to close via minimal tactic one-liner
  - L176 [soft] `skeletal-proof` in `theorem spectralProjector_star_of_isSelfAdjoint` — proof appears to close via minimal tactic one-liner
  - L184 [soft] `skeletal-proof` in `theorem spectralProjector_isSelfAdjoint_of_isSelfAdjoint` — proof appears to close via minimal tactic one-liner
  - L216 [soft] `skeletal-proof` in `theorem chiralAnomalyOperator_star_eq_neg_of_isSelfAdjoint` — proof appears to close via minimal tactic one-liner
  - L235 [soft] `skeletal-proof` in `theorem rightChiralAnomalyOperator_star_eq_neg_of_isSelfAdjoint` — proof appears to close via minimal tactic one-liner
  - L248 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L256 [soft] `skeletal-proof` in `theorem mpRangeProjector_eq_metricProjector` — proof appears to close via minimal tactic one-liner
  - L276 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L305 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L338 [soft] `skeletal-proof` in `theorem metricProjector_star` — proof appears to close via minimal tactic one-liner
  - L344 [soft] `skeletal-proof` in `theorem spectralProjector_star_eq` — proof appears to close via minimal tactic one-liner
  - L354 [soft] `skeletal-proof` in `theorem mpRangeProjector_star` — proof appears to close via minimal tactic one-liner
  - L380 [soft] `skeletal-proof` in `theorem chiralAnomalyOperator_star_eq_neg` — proof appears to close via minimal tactic one-liner
  - L394 [soft] `skeletal-proof` in `theorem rightChiralAnomalyOperator_star_eq_neg` — proof appears to close via minimal tactic one-liner
  - L407 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L423 [soft] `skeletal-proof` in `theorem specialConformal_eq_modularInversion_translation` — proof appears to close via minimal tactic one-liner
  - L433 [soft] `skeletal-proof` in `theorem translation_eq_modularInversion_specialConformal` — proof appears to close via minimal tactic one-liner
  - L458 [soft] `skeletal-proof` in `theorem dilation_eq_half_sub_mp_projectors` — proof appears to close via minimal tactic one-liner
  - L532 [advisory] `local-hypothesis-injection` in `abbrev leftChiralAnomalyOperator` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L535 [advisory] `local-hypothesis-injection` in `abbrev leftChiralAnomalyOperator` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L538 [advisory] `local-hypothesis-injection` in `abbrev leftChiralAnomalyOperator` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L541 [advisory] `local-hypothesis-injection` in `abbrev leftChiralAnomalyOperator` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L552 [advisory] `local-hypothesis-injection` in `abbrev leftChiralAnomalyOperator` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L563 [advisory] `local-hypothesis-injection` in `abbrev leftChiralAnomalyOperator` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L568 [advisory] `local-hypothesis-injection` in `abbrev leftChiralAnomalyOperator` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L570 [advisory] `local-hypothesis-injection` in `abbrev leftChiralAnomalyOperator` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L572 [advisory] `local-hypothesis-injection` in `abbrev leftChiralAnomalyOperator` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L575 [advisory] `local-hypothesis-injection` in `abbrev leftChiralAnomalyOperator` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L667 [soft] `skeletal-proof` in `theorem singularEinsteinAnomaly_eq_neg_rightChiralAnomaly` — proof appears to close via minimal tactic one-liner
  - L688 [soft] `skeletal-proof` in `theorem singularEinsteinAnomaly_eq_neg_leftChiralAnomaly_of_projectorAgreement` — proof appears to close via minimal tactic one-liner
  - L766 [soft] `skeletal-proof` in `theorem spectralProjector_commutator_dilation_eq_neg_half_leftChiralAnomaly_of_rightProjector_commute` — proof appears to close via minimal tactic one-liner
  - L778 [soft] `skeletal-proof` in `theorem rightProjector_commute_of_projectorAgreement_of_metricProjector_commute` — proof appears to close via minimal tactic one-liner
  - L816 [soft] `skeletal-proof` in `theorem spectralProjector_commutator_dilation_eq_zero_of_rightProjector_commute_of_leftChiralAnomaly_eq_zero` — proof appears to close via minimal tactic one-liner
  - L829 [soft] `skeletal-proof` in `theorem chiral_commutation_link` — proof appears to close via minimal tactic one-liner
  - L841 [soft] `skeletal-proof` in `theorem chiralAnomalyOperator_eq_zero_iff_projectors_commute` — proof appears to close via minimal tactic one-liner
  - L848 [soft] `skeletal-proof` in `theorem leftChiralAnomalyOperator_eq_zero_iff_projectors_commute` — proof appears to close via minimal tactic one-liner
  - L881 [advisory] `existential-packaging` in `theorem exists_of_spectralTriple` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L896 [advisory] `existential-packaging` in `theorem exists_of_infoSpectralTriple` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

