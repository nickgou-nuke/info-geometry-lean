# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:51.946207+00:00`
Root: `lean/InfoGeometry/Canonical/RelativeModularSingularization.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **31**
- Hard: **0**
- Soft: **24**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RelativeModularSingularization.lean` | `advisory` | 55 | 0 | 24 | 7 | 31 |

## Findings by file

### `lean/InfoGeometry/Canonical/RelativeModularSingularization.lean`
- module: `InfoGeometry.Canonical.RelativeModularSingularization`
- status: `advisory`
- debt_score: `55`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L42 [advisory] `local-hypothesis-injection` in `theorem relativeDensity_mul_reverse` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L49 [advisory] `local-hypothesis-injection` in `theorem reverse_relativeDensity_mul` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L55 [advisory] `existential-packaging` in `def supportProjector` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L59 [soft] `simp-law-injection` in `simp-declaration supportProjector_diag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L65 [soft] `simp-law-injection` in `simp-declaration supportProjector_offdiag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L71 [soft] `simp-law-injection` in `simp-declaration supportProjector_idempotent` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L82 [soft] `simp-law-injection` in `simp-declaration supportProjector_star` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L90 [advisory] `existential-packaging` in `theorem supportProjector_ne_zero_of_mem` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L90 [soft] `skeletal-proof` in `theorem supportProjector_ne_zero_of_mem` — proof appears to close via minimal tactic one-liner
  - L94 [advisory] `local-hypothesis-injection` in `theorem supportProjector_ne_zero_of_mem` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L99 [soft] `skeletal-proof` in `theorem supportProjector_ne_one_of_not_mem` — proof appears to close via minimal tactic one-liner
  - L103 [advisory] `local-hypothesis-injection` in `theorem supportProjector_ne_one_of_not_mem` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L126 [soft] `simp-law-injection` in `simp-declaration singularRelativeModularOperator_diag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L132 [soft] `simp-law-injection` in `simp-declaration singularRelativeModularOperator_offdiag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L137 [soft] `simp-law-injection` in `simp-declaration singularRelativeModularPseudoInverse_diag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L143 [soft] `simp-law-injection` in `simp-declaration singularRelativeModularPseudoInverse_offdiag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L201 [soft] `simp-law-injection` in `simp-declaration supportProjector_mul_singularRelativeModularOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L211 [soft] `simp-law-injection` in `simp-declaration singularRelativeModularOperator_mul_supportProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L221 [soft] `simp-law-injection` in `simp-declaration supportProjector_mul_singularRelativeModularPseudoInverse` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L231 [soft] `simp-law-injection` in `simp-declaration singularRelativeModularPseudoInverse_mul_supportProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L338 [soft] `simp-law-injection` in `simp-declaration drazinProjection_eq_supportProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L347 [soft] `simp-law-injection` in `simp-declaration moorePenroseRightProjector_eq_supportProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L356 [soft] `simp-law-injection` in `simp-declaration moorePenroseLeftProjector_eq_supportProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L419 [soft] `simp-law-injection` in `simp-declaration relativeModularPseudoVolumeShadow_pos` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L428 [soft] `simp-law-injection` in `simp-declaration relativeModularPseudoVolumeShadow_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L436 [soft] `simp-law-injection` in `simp-declaration relativeModularPseudoVolumeShadow_univ` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L478 [soft] `simp-law-injection` in `simp-declaration relativeModularPseudoVolumePotential_univ` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L503 [soft] `simp-law-injection` in `simp-declaration relativeModularPseudoBerezinianShadow_pos` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L562 [soft] `simp-law-injection` in `simp-declaration relativeModularPseudoBerezinianShadow_univ` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L570 [soft] `simp-law-injection` in `simp-declaration relativeModularPseudoBerezinianPotential_univ` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

