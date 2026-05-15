# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:43.187010+00:00`
Root: `lean/InfoGeometry/Canonical/BogoliubovClosedForms.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **24**
- Hard: **0**
- Soft: **15**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/BogoliubovClosedForms.lean` | `advisory` | 39 | 0 | 15 | 9 | 24 |

## Findings by file

### `lean/InfoGeometry/Canonical/BogoliubovClosedForms.lean`
- module: `InfoGeometry.Canonical.BogoliubovClosedForms`
- status: `advisory`
- debt_score: `39`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L17 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L19 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L20 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L33 [advisory] `local-hypothesis-injection` in `lemma smul_pow_even_of_sq_eq_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L67 [advisory] `local-hypothesis-injection` in `lemma smul_pow_even_of_sq_eq_neg_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L87 [advisory] `local-hypothesis-injection` in `lemma smul_pow_even_of_sq_eq_neg_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L90 [advisory] `local-hypothesis-injection` in `lemma smul_pow_even_of_sq_eq_neg_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L175 [soft] `skeletal-proof` in `theorem JBoost_eq_cosh_add_sinh_modular_j` — proof appears to close via minimal tactic one-liner
  - L189 [soft] `skeletal-proof` in `theorem epsilonBoost_eq_cosh_add_sinh_spectral_epsilon` — proof appears to close via minimal tactic one-liner
  - L203 [soft] `skeletal-proof` in `theorem KRotation_eq_cos_add_sin_complex_i` — proof appears to close via minimal tactic one-liner
  - L210 [soft] `simp-law-injection` in `simp-declaration JBoost_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L216 [soft] `simp-law-injection` in `simp-declaration JBoost_apply_modular_j` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L221 [soft] `simp-law-injection` in `simp-declaration epsilonBoost_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L228 [soft] `simp-law-injection` in `simp-declaration epsilonBoost_apply_spectral_epsilon` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L234 [soft] `simp-law-injection` in `simp-declaration KRotation_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L240 [soft] `simp-law-injection` in `simp-declaration KRotation_apply_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L245 [soft] `skeletal-proof` in `theorem comp_KRotation_eq_KRotation_comp_of_IsPhaseLinear` — proof appears to close via minimal tactic one-liner
  - L267 [soft] `skeletal-proof` in `theorem comp_KRotation_eq_KRotation_neg_comp_of_IsPhaseAntilinear` — proof appears to close via minimal tactic one-liner
  - L290 [soft] `skeletal-proof` in `theorem kreinInner_KRotation_neg_left_KRotation_right` — proof appears to close via minimal tactic one-liner
  - L321 [advisory] `local-hypothesis-injection` in `theorem kreinInner_KRotation_neg_left_KRotation_right` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L337 [soft] `skeletal-proof` in `theorem spectral_epsilon_comp_epsilonBoost` — proof appears to close via minimal tactic one-liner
  - L355 [soft] `skeletal-proof` in `theorem spectral_epsilon_comp_JBoost` — proof appears to close via minimal tactic one-liner
  - L373 [soft] `skeletal-proof` in `theorem spectral_epsilon_comp_KRotation` — proof appears to close via minimal tactic one-liner

