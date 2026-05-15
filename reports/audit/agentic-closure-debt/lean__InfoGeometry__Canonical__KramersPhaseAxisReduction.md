# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:24.111724+00:00`
Root: `lean/InfoGeometry/Canonical/KramersPhaseAxisReduction.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **36**
- Hard: **0**
- Soft: **6**
- Advisory: **30**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/KramersPhaseAxisReduction.lean` | `advisory` | 42 | 0 | 6 | 30 | 36 |

## Findings by file

### `lean/InfoGeometry/Canonical/KramersPhaseAxisReduction.lean`
- module: `InfoGeometry.Canonical.KramersPhaseAxisReduction`
- status: `advisory`
- debt_score: `42`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L28 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L30 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L42 [soft] `skeletal-proof` in `theorem phaseAxisRightFactor_comp_phaseAxis_eq` — proof appears to close via minimal tactic one-liner
  - L61 [soft] `skeletal-proof` in `theorem phaseAxisRightFactor_unique` — proof appears to close via minimal tactic one-liner
  - L83 [advisory] `existential-packaging` in `theorem kramers_factor_through_phaseAxis` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L107 [advisory] `existential-packaging` in `theorem kramers_unique_phaseAxis_factor` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L120 [soft] `skeletal-proof` in `theorem theta_eq_R_comp_phaseAxisK_of_phaseReduction` — proof appears to close via minimal tactic one-liner
  - L137 [advisory] `local-hypothesis-injection` in `theorem phaseReduction_unique_of_commute_phaseAxisK` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L140 [advisory] `local-hypothesis-injection` in `theorem phaseReduction_unique_of_commute_phaseAxisK` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L168 [advisory] `existential-packaging` in `theorem abstract_kramers_diverges_from_intrinsic_of_not_phaseReduction` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L173 [advisory] `local-hypothesis-injection` in `theorem abstract_kramers_diverges_from_intrinsic_of_not_phaseReduction` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L186 [advisory] `existential-packaging` in `theorem abstract_kramers_phaseReduction_package` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L206 [soft] `skeletal-proof` in `theorem eq_zero_of_kLinear_and_kAntilinear` — proof appears to close via minimal tactic one-liner
  - L212 [advisory] `local-hypothesis-injection` in `theorem eq_zero_of_kLinear_and_kAntilinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L213 [advisory] `local-hypothesis-injection` in `theorem eq_zero_of_kLinear_and_kAntilinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L214 [advisory] `local-hypothesis-injection` in `theorem eq_zero_of_kLinear_and_kAntilinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L220 [advisory] `local-hypothesis-injection` in `theorem eq_zero_of_kLinear_and_kAntilinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L222 [advisory] `local-hypothesis-injection` in `theorem eq_zero_of_kLinear_and_kAntilinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L223 [advisory] `local-hypothesis-injection` in `theorem eq_zero_of_kLinear_and_kAntilinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L225 [advisory] `local-hypothesis-injection` in `theorem eq_zero_of_kLinear_and_kAntilinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L228 [advisory] `local-hypothesis-injection` in `theorem eq_zero_of_kLinear_and_kAntilinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L230 [advisory] `local-hypothesis-injection` in `theorem eq_zero_of_kLinear_and_kAntilinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L242 [soft] `skeletal-proof` in `theorem kramers_not_scalar_multiple_phaseAxis` — proof appears to close via minimal tactic one-liner
  - L250 [advisory] `local-hypothesis-injection` in `theorem kramers_not_scalar_multiple_phaseAxis` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L252 [advisory] `local-hypothesis-injection` in `theorem kramers_not_scalar_multiple_phaseAxis` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L254 [advisory] `local-hypothesis-injection` in `theorem kramers_not_scalar_multiple_phaseAxis` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L255 [advisory] `local-hypothesis-injection` in `theorem kramers_not_scalar_multiple_phaseAxis` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L266 [advisory] `local-hypothesis-injection` in `theorem kramers_not_scalar_multiple_phaseAxis` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L273 [advisory] `local-hypothesis-injection` in `theorem kramers_not_scalar_multiple_phaseAxis` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L283 [soft] `skeletal-proof` in `theorem kramers_not_kLinear` — proof appears to close via minimal tactic one-liner
  - L288 [advisory] `local-hypothesis-injection` in `theorem kramers_not_kLinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L291 [advisory] `local-hypothesis-injection` in `theorem kramers_not_kLinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L293 [advisory] `local-hypothesis-injection` in `theorem kramers_not_kLinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L295 [advisory] `local-hypothesis-injection` in `theorem kramers_not_kLinear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L304 [advisory] `existential-packaging` in `theorem kramers_no_scalar_phaseAxis_collapse` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

