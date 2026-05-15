# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:44.953558+00:00`
Root: `lean/InfoGeometry/Canonical/BottPeriodicity.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **24**
- Hard: **0**
- Soft: **12**
- Advisory: **12**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/BottPeriodicity.lean` | `advisory` | 36 | 0 | 12 | 12 | 24 |

## Findings by file

### `lean/InfoGeometry/Canonical/BottPeriodicity.lean`
- module: `InfoGeometry.Canonical.BottPeriodicity`
- status: `advisory`
- debt_score: `36`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L12 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L14 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L15 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L16 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L17 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L40 [soft] `simp-law-injection` in `simp-declaration tensorModularJ_tmul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L45 [soft] `simp-law-injection` in `simp-declaration tensorSpectralEpsilon_tmul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L50 [soft] `simp-law-injection` in `simp-declaration tensorModularJ_comp_tmul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L55 [advisory] `local-hypothesis-injection` in `def tensorSpectralEpsilon` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L58 [advisory] `local-hypothesis-injection` in `def tensorSpectralEpsilon` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L62 [soft] `simp-law-injection` in `simp-declaration tensorSpectralEpsilon_comp_tmul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L68 [advisory] `local-hypothesis-injection` in `def tensorSpectralEpsilon` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L71 [advisory] `local-hypothesis-injection` in `def tensorSpectralEpsilon` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L104 [soft] `simp-law-injection` in `simp-declaration bottGeneratorInjection_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L114 [soft] `simp-law-injection` in `simp-declaration bottStepEquiv_symm_left_generator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L123 [soft] `simp-law-injection` in `simp-declaration bottStepEquiv_symm_right_generator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L143 [soft] `simp-law-injection` in `simp-declaration bottGeneratorInjection_zero_left` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L148 [advisory] `local-hypothesis-injection` in `abbrev bott_step_periodicity` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L152 [soft] `simp-law-injection` in `simp-declaration bottGeneratorInjection_zero_right` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L157 [advisory] `local-hypothesis-injection` in `abbrev bott_step_periodicity` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L267 [soft] `simp-law-injection` in `simp-declaration twistedGeneratorPattern_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L274 [soft] `simp-law-injection` in `simp-declaration gradedProdInjection_on_generator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L285 [soft] `simp-law-injection` in `simp-declaration gradedProdInjection_matches_pattern_unit` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

