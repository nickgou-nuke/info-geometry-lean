# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:49.786598+00:00`
Root: `lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **40**
- Hard: **0**
- Soft: **29**
- Advisory: **11**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean` | `advisory` | 69 | 0 | 29 | 11 | 40 |

## Findings by file

### `lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean`
- module: `InfoGeometry.Canonical.CertifiedInverseKernel`
- status: `advisory`
- debt_score: `69`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L24 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L38 [soft] `law-field-locker` in `structure-field InverseKernel.A` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L39 [soft] `law-field-locker` in `structure-field InverseKernel.A_D` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L40 [soft] `law-field-locker` in `structure-field InverseKernel.A_MP` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L56 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L90 [soft] `skeletal-proof` in `theorem chiralAnomaly_eq_mismatch_commutator_metric` — proof appears to close via minimal tactic one-liner
  - L100 [soft] `skeletal-proof` in `theorem projectorMismatch_eq_zero_iff` — proof appears to close via minimal tactic one-liner
  - L108 [soft] `skeletal-proof` in `theorem chiralScale_eq_zero_iff_chiralAnomaly_eq_zero` — proof appears to close via minimal tactic one-liner
  - L113 [soft] `skeletal-proof` in `theorem rightChiralAnomaly_eq_chiralAnomaly_of_projectorAgreement` — proof appears to close via minimal tactic one-liner
  - L129 [soft] `skeletal-proof` in `theorem spectralProjector_commutator_dilationGap_eq_neg_half_anomaly_of_rightProjector_commute` — proof appears to close via minimal tactic one-liner
  - L136 [advisory] `local-hypothesis-injection` in `theorem spectralProjector_commutator_dilationGap_eq_neg_half_anomaly_of_rightProjector_commute` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L153 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L202 [soft] `skeletal-proof` in `theorem spectralProjector_idempotent` — proof appears to close via minimal tactic one-liner
  - L209 [soft] `skeletal-proof` in `theorem mpRangeProjector_idempotent` — proof appears to close via minimal tactic one-liner
  - L216 [soft] `skeletal-proof` in `theorem metricProjector_idempotent` — proof appears to close via minimal tactic one-liner
  - L223 [soft] `skeletal-proof` in `theorem mpRangeProjector_star` — proof appears to close via minimal tactic one-liner
  - L230 [soft] `skeletal-proof` in `theorem metricProjector_star` — proof appears to close via minimal tactic one-liner
  - L237 [soft] `skeletal-proof` in `theorem spectralProjector_star_of_selfAdjoint` — proof appears to close via minimal tactic one-liner
  - L305 [soft] `skeletal-proof` in `theorem chiralAnomaly_eq_mismatch_commutator_metric` — proof appears to close via minimal tactic one-liner
  - L314 [soft] `skeletal-proof` in `theorem projectorMismatch_eq_zero_iff` — proof appears to close via minimal tactic one-liner
  - L321 [soft] `skeletal-proof` in `theorem chiralScale_eq_zero_iff_chiralAnomaly_eq_zero` — proof appears to close via minimal tactic one-liner
  - L328 [soft] `skeletal-proof` in `theorem rightChiralAnomaly_eq_chiralAnomaly_of_projectorAgreement` — proof appears to close via minimal tactic one-liner
  - L337 [soft] `skeletal-proof` in `theorem GammaG_eq_two_smul_dilationGap` — proof appears to close via minimal tactic one-liner
  - L345 [advisory] `local-hypothesis-injection` in `theorem GammaG_eq_two_smul_dilationGap` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L354 [soft] `skeletal-proof` in `theorem spectralProjector_commutator_dilationGap_eq_half_sub_anomalies` — proof appears to close via minimal tactic one-liner
  - L363 [soft] `skeletal-proof` in `theorem spectralProjector_commutator_dilationGap_eq_neg_half_anomaly_of_rightProjector_commute` — proof appears to close via minimal tactic one-liner
  - L373 [soft] `skeletal-proof` in `theorem spectralProjector_commutator_dilationGap_eq_zero_of_rightProjector_commute_of_chiralScale_eq_zero` — proof appears to close via minimal tactic one-liner
  - L383 [soft] `skeletal-proof` in `theorem spectralProjector_commutator_GammaG_eq_sub_anomalies` — proof appears to close via minimal tactic one-liner
  - L445 [advisory] `local-hypothesis-injection` in `theorem projectorMismatch_fixed_under_spectralGradingFlow_of_projector_commute` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L447 [advisory] `local-hypothesis-injection` in `theorem projectorMismatch_fixed_under_spectralGradingFlow_of_projector_commute` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L454 [advisory] `local-hypothesis-injection` in `theorem projectorMismatch_fixed_under_spectralGradingFlow_of_projector_commute` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L506 [soft] `skeletal-proof` in `theorem chiralAnomaly_anticommutes_GammaS` — proof appears to close via minimal tactic one-liner
  - L512 [advisory] `local-hypothesis-injection` in `theorem chiralAnomaly_anticommutes_GammaS` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L527 [soft] `skeletal-proof` in `theorem rightChiralAnomaly_anticommutes_GammaS` — proof appears to close via minimal tactic one-liner
  - L533 [advisory] `local-hypothesis-injection` in `theorem rightChiralAnomaly_anticommutes_GammaS` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L564 [soft] `skeletal-proof` in `theorem chiralAnomaly_spectralAdjointFlow_mem_noncompact` — proof appears to close via minimal tactic one-liner
  - L580 [soft] `skeletal-proof` in `theorem rightChiralAnomaly_spectralAdjointFlow_mem_noncompact` — proof appears to close via minimal tactic one-liner
  - L624 [soft] `skeletal-proof` in `theorem spectralProjector_commutator_spectralAdjointFlow_dilationGap_eq_half_sub_anomaly_flows` — proof appears to close via minimal tactic one-liner
  - L705 [soft] `skeletal-proof` in `theorem spectralProjector_commutator_spectralAdjointFlow_dilationGap_eq_mul_spectralGradingFlow_neg_two` — proof appears to close via minimal tactic one-liner

