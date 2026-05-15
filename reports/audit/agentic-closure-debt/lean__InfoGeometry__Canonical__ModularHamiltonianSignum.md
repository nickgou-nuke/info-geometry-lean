# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:29.237360+00:00`
Root: `lean/InfoGeometry/Canonical/ModularHamiltonianSignum.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **42**
- Hard: **0**
- Soft: **25**
- Advisory: **17**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ModularHamiltonianSignum.lean` | `advisory` | 67 | 0 | 25 | 17 | 42 |

## Findings by file

### `lean/InfoGeometry/Canonical/ModularHamiltonianSignum.lean`
- module: `InfoGeometry.Canonical.ModularHamiltonianSignum`
- status: `advisory`
- debt_score: `67`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L33 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L35 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L36 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L37 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L38 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L39 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L67 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L67 [soft] `section-law-variable` in `variable hJ` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L68 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L68 [soft] `section-law-variable` in `variable hS` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L69 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L69 [soft] `section-law-variable` in `variable hJS` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L147 [soft] `skeletal-proof` in `theorem signumCommutator_one_left` — proof appears to close via minimal tactic one-liner
  - L153 [soft] `skeletal-proof` in `theorem signumCommutator_one_right` — proof appears to close via minimal tactic one-liner
  - L159 [soft] `skeletal-proof` in `theorem signumAnticommutator_one_left` — proof appears to close via minimal tactic one-liner
  - L166 [soft] `skeletal-proof` in `theorem signumAnticommutator_one_right` — proof appears to close via minimal tactic one-liner
  - L173 [soft] `skeletal-proof` in `theorem signumCommutator_reflection_signum` — proof appears to close via minimal tactic one-liner
  - L195 [soft] `skeletal-proof` in `theorem signumCommutator_reflection_phaseAxis` — proof appears to close via minimal tactic one-liner
  - L228 [soft] `skeletal-proof` in `theorem signumCommutator_phaseAxis_signum` — proof appears to close via minimal tactic one-liner
  - L314 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L314 [soft] `section-law-variable` in `variable hJ` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L315 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L315 [soft] `section-law-variable` in `variable hS` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L316 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L316 [soft] `section-law-variable` in `variable hJS` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L328 [soft] `skeletal-proof` in `theorem modularSignum_phaseAxis_sq` — proof appears to close via minimal tactic one-liner
  - L333 [advisory] `local-hypothesis-injection` in `theorem modularSignum_phaseAxis_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L337 [advisory] `local-hypothesis-injection` in `theorem modularSignum_phaseAxis_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L339 [advisory] `local-hypothesis-injection` in `theorem modularSignum_phaseAxis_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L341 [advisory] `local-hypothesis-injection` in `theorem modularSignum_phaseAxis_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L404 [soft] `skeletal-proof` in `theorem modularSignumCommutator_reflection_signum` — proof appears to close via minimal tactic one-liner
  - L426 [soft] `skeletal-proof` in `theorem modularSignumCommutator_reflection_phaseAxis` — proof appears to close via minimal tactic one-liner
  - L459 [soft] `skeletal-proof` in `theorem modularSignumCommutator_phaseAxis_signum` — proof appears to close via minimal tactic one-liner
  - L526 [soft] `skeletal-proof` in `theorem epsilon_eq_projector_sign` — proof appears to close via minimal tactic one-liner
  - L532 [soft] `skeletal-proof` in `theorem epsilon_eq_spectral_projector_sign` — proof appears to close via minimal tactic one-liner
  - L572 [soft] `skeletal-proof` in `theorem unruh_modularHamiltonian_eq_epsilon` — proof appears to close via minimal tactic one-liner
  - L588 [soft] `skeletal-proof` in `theorem unruh_modularHamiltonian_sq_one` — proof appears to close via minimal tactic one-liner
  - L595 [soft] `skeletal-proof` in `theorem unruh_modularHamiltonian_mul_plusProjector` — proof appears to close via minimal tactic one-liner
  - L602 [soft] `skeletal-proof` in `theorem unruh_modularHamiltonian_mul_minusProjector` — proof appears to close via minimal tactic one-liner
  - L609 [soft] `skeletal-proof` in `theorem plusProjector_mul_unruh_modularHamiltonian` — proof appears to close via minimal tactic one-liner
  - L616 [soft] `skeletal-proof` in `theorem minusProjector_mul_unruh_modularHamiltonian` — proof appears to close via minimal tactic one-liner

