# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:13.797290+00:00`
Root: `lean/InfoGeometry/Canonical/HestenesComplexTranslation.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **36**
- Hard: **0**
- Soft: **21**
- Advisory: **15**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/HestenesComplexTranslation.lean` | `advisory` | 57 | 0 | 21 | 15 | 36 |

## Findings by file

### `lean/InfoGeometry/Canonical/HestenesComplexTranslation.lean`
- module: `InfoGeometry.Canonical.HestenesComplexTranslation`
- status: `advisory`
- debt_score: `57`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L40 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L42 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L43 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L44 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L54 [soft] `simp-law-injection` in `simp-declaration hestenesScalar_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L56 [soft] `skeletal-proof` in `theorem hestenesScalar_zero` — proof appears to close via minimal tactic one-liner
  - L59 [soft] `simp-law-injection` in `simp-declaration hestenesScalar_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L61 [soft] `skeletal-proof` in `theorem hestenesScalar_one` — proof appears to close via minimal tactic one-liner
  - L64 [soft] `simp-law-injection` in `simp-declaration hestenesScalar_I` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L66 [soft] `skeletal-proof` in `theorem hestenesScalar_I` — proof appears to close via minimal tactic one-liner
  - L72 [soft] `skeletal-proof` in `theorem hestenesScalar_I_sq` — proof appears to close via minimal tactic one-liner
  - L88 [soft] `simp-law-injection` in `simp-declaration hestenesCoeff_zero_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L90 [soft] `skeletal-proof` in `theorem hestenesCoeff_zero_zero` — proof appears to close via minimal tactic one-liner
  - L93 [soft] `simp-law-injection` in `simp-declaration hestenesCoeff_one_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L95 [soft] `skeletal-proof` in `theorem hestenesCoeff_one_zero` — proof appears to close via minimal tactic one-liner
  - L98 [soft] `simp-law-injection` in `simp-declaration hestenesCoeff_zero_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L100 [soft] `skeletal-proof` in `theorem hestenesCoeff_zero_one` — proof appears to close via minimal tactic one-liner
  - L108 [soft] `skeletal-proof` in `theorem hestenesCoeff_I_sq` — proof appears to close via minimal tactic one-liner
  - L118 [soft] `skeletal-proof` in `theorem hestenesScalar_eq_hestenesCoeff_real_coeff` — proof appears to close via minimal tactic one-liner
  - L134 [soft] `skeletal-proof` in `theorem hestenesCoeff_mul` — proof appears to close via minimal tactic one-liner
  - L140 [advisory] `local-hypothesis-injection` in `theorem hestenesCoeff_mul` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L148 [advisory] `local-hypothesis-injection` in `theorem hestenesCoeff_mul` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L153 [advisory] `local-hypothesis-injection` in `theorem hestenesCoeff_mul` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L172 [soft] `skeletal-proof` in `theorem hestenesCoeff_isPhaseLinear` — proof appears to close via minimal tactic one-liner
  - L178 [advisory] `local-hypothesis-injection` in `theorem hestenesCoeff_isPhaseLinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L187 [advisory] `local-hypothesis-injection` in `theorem hestenesCoeff_isPhaseLinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L205 [soft] `skeletal-proof` in `theorem modular_j_conjugates_hestenesCoeff_of_fixed` — proof appears to close via minimal tactic one-liner
  - L211 [advisory] `local-hypothesis-injection` in `theorem modular_j_conjugates_hestenesCoeff_of_fixed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L212 [advisory] `local-hypothesis-injection` in `theorem modular_j_conjugates_hestenesCoeff_of_fixed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L220 [advisory] `local-hypothesis-injection` in `theorem modular_j_conjugates_hestenesCoeff_of_fixed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L244 [soft] `skeletal-proof` in `theorem hestenesScalar_apply_eq_complexAction` — proof appears to close via minimal tactic one-liner
  - L262 [soft] `skeletal-proof` in `theorem commutes_hestenesScalar_of_isPhaseLinear` — proof appears to close via minimal tactic one-liner
  - L268 [advisory] `local-hypothesis-injection` in `theorem commutes_hestenesScalar_of_isPhaseLinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L272 [advisory] `local-hypothesis-injection` in `theorem commutes_hestenesScalar_of_isPhaseLinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L294 [soft] `skeletal-proof` in `theorem modular_j_conjugates_complex_i` — proof appears to close via minimal tactic one-liner

