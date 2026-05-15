# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:06.702545+00:00`
Root: `lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **42**
- Hard: **0**
- Soft: **32**
- Advisory: **10**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean` | `advisory` | 74 | 0 | 32 | 10 | 42 |

## Findings by file

### `lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean`
- module: `InfoGeometry.Canonical.EinsteinAnomalyOperator`
- status: `advisory`
- debt_score: `74`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L16 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L18 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L20 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L55 [soft] `simp-law-injection` in `simp-declaration liftedChiralAnomalyOperator_apply_to_doubled` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L63 [soft] `simp-law-injection` in `simp-declaration liftedRightChiralAnomalyOperator_apply_to_doubled` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L69 [soft] `simp-law-injection` in `simp-declaration liftedEinsteinAnomalyOperator_apply_to_doubled` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L89 [advisory] `local-hypothesis-injection` in `theorem dualSheetLift_isPhaseLinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L94 [soft] `skeletal-proof` in `theorem liftedEinsteinAnomalyOperator_isPhaseLinear` — proof appears to close via minimal tactic one-liner
  - L105 [soft] `simp-law-injection` in `simp-declaration dualSheetLift_neg` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L113 [soft] `skeletal-proof` in `theorem dualSheetLift_eq_zero_iff` — proof appears to close via minimal tactic one-liner
  - L138 [soft] `skeletal-proof` in `theorem liftedRightChiralAnomalyOperator_eq_zero_iff` — proof appears to close via minimal tactic one-liner
  - L146 [soft] `skeletal-proof` in `theorem liftedEinsteinAnomalyOperator_eq_zero_iff` — proof appears to close via minimal tactic one-liner
  - L162 [soft] `skeletal-proof` in `theorem liftedRightChiralAnomalyOperator_ne_zero_iff` — proof appears to close via minimal tactic one-liner
  - L169 [soft] `skeletal-proof` in `theorem liftedEinsteinAnomalyOperator_ne_zero_iff` — proof appears to close via minimal tactic one-liner
  - L176 [soft] `simp-law-injection` in `simp-declaration plusProjectorFlux_liftedChiralAnomalyOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L181 [soft] `simp-law-injection` in `simp-declaration minusProjectorFlux_liftedChiralAnomalyOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L186 [soft] `simp-law-injection` in `simp-declaration plusProjectorFlux_liftedEinsteinAnomalyOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L190 [soft] `simp-law-injection` in `simp-declaration minusProjectorFlux_liftedEinsteinAnomalyOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L209 [soft] `skeletal-proof` in `theorem liftedEinsteinAnomalyOperator_eq_neg_liftedLeftChiralAnomalyOperator_of_projectorAgreement` — proof appears to close via minimal tactic one-liner
  - L236 [soft] `skeletal-proof` in `theorem liftedEinsteinAnomalyOperator_eq_neg_liftedProjectorObstructionOperator_of_projectorAgreement` — proof appears to close via minimal tactic one-liner
  - L307 [soft] `skeletal-proof` in `theorem liftedEinsteinAnomalyOperator_relativeModularDeriv_eq_modularGaugeDeriv_of_commute_scalePart` — proof appears to close via minimal tactic one-liner
  - L323 [soft] `skeletal-proof` in `theorem liftedEinsteinAnomalyOperator_relativeModularDeriv_eq_zero_of_commute_parts` — proof appears to close via minimal tactic one-liner
  - L415 [soft] `skeletal-proof` in `theorem bogoliubovConjugate_liftedLeftChiralAnomalyOperator_eq_exp_mul_mul_exp_neg` — proof appears to close via minimal tactic one-liner
  - L428 [soft] `skeletal-proof` in `theorem bogoliubovConjugate_liftedRightChiralAnomalyOperator_eq_exp_mul_mul_exp_neg` — proof appears to close via minimal tactic one-liner
  - L441 [soft] `skeletal-proof` in `theorem bogoliubovConjugate_liftedLeftChiralAnomalyOperator_eq_self_of_commute_generator` — proof appears to close via minimal tactic one-liner
  - L457 [soft] `skeletal-proof` in `theorem bogoliubovConjugate_liftedRightChiralAnomalyOperator_eq_self_of_commute_generator` — proof appears to close via minimal tactic one-liner
  - L513 [soft] `skeletal-proof` in `theorem bogoliubovConjugate_liftedLeftChiralAnomalyOperator_ne_zero_iff_of_commute_generator` — proof appears to close via minimal tactic one-liner
  - L529 [soft] `skeletal-proof` in `theorem bogoliubovConjugate_liftedRightChiralAnomalyOperator_ne_zero_iff_of_commute_generator` — proof appears to close via minimal tactic one-liner
  - L557 [soft] `skeletal-proof` in `theorem bogoliubovConjugate_liftedEinsteinAnomalyOperator_eq_exp_mul_mul_exp_neg` — proof appears to close via minimal tactic one-liner
  - L570 [soft] `skeletal-proof` in `theorem deriv_bogoliubovConjugate_liftedEinsteinAnomalyOperator_at_zero_eq_relativeModularDeriv` — proof appears to close via minimal tactic one-liner
  - L623 [soft] `skeletal-proof` in `theorem expTransport_liftedEinsteinAnomalyOperator_eq_self_of_commute_generator` — proof appears to close via minimal tactic one-liner
  - L670 [soft] `skeletal-proof` in `theorem bogoliubovConjugate_liftedEinsteinAnomalyOperator_eq_self_of_commute_generator` — proof appears to close via minimal tactic one-liner
  - L705 [soft] `skeletal-proof` in `theorem bogoliubovConjugate_liftedEinsteinAnomalyOperator_ne_zero_iff_of_commute_generator` — proof appears to close via minimal tactic one-liner
  - L725 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L727 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L729 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L747 [soft] `skeletal-proof` in `theorem liftedEinsteinAnomalyOperator_eq_neg_liftedRightChiralAnomalyOperator` — proof appears to close via minimal tactic one-liner
  - L757 [soft] `skeletal-proof` in `theorem liftedEinsteinAnomalyOperator_isPhaseLinear` — proof appears to close via minimal tactic one-liner
  - L773 [advisory] `local-hypothesis-injection` in `theorem liftedLeftChiralAnomalyOperator_star_eq_neg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L805 [advisory] `local-hypothesis-injection` in `theorem liftedRightChiralAnomalyOperator_star_eq_neg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L829 [soft] `skeletal-proof` in `theorem liftedEinsteinAnomalyOperator_star_eq_neg` — proof appears to close via minimal tactic one-liner

