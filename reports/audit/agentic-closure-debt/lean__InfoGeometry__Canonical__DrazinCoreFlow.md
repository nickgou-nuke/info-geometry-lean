# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:02.201571+00:00`
Root: `lean/InfoGeometry/Canonical/DrazinCoreFlow.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **25**
- Hard: **0**
- Soft: **11**
- Advisory: **14**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DrazinCoreFlow.lean` | `advisory` | 36 | 0 | 11 | 14 | 25 |

## Findings by file

### `lean/InfoGeometry/Canonical/DrazinCoreFlow.lean`
- module: `InfoGeometry.Canonical.DrazinCoreFlow`
- status: `advisory`
- debt_score: `36`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L28 [soft] `skeletal-proof` in `theorem projection_mul_eq_mul_projection` — proof appears to close via minimal tactic one-liner
  - L44 [soft] `skeletal-proof` in `theorem commute_complementaryProjection` — proof appears to close via minimal tactic one-liner
  - L50 [advisory] `local-hypothesis-injection` in `theorem commute_complementaryProjection` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L75 [soft] `skeletal-proof` in `theorem pow_mul_complementaryProjection_eq_zero_of_le` — proof appears to close via minimal tactic one-liner
  - L81 [advisory] `local-hypothesis-injection` in `theorem pow_mul_complementaryProjection_eq_zero_of_le` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L108 [soft] `skeletal-proof` in `theorem nilpotent_pow_succ_eq_pow_mul_complementaryProjection` — proof appears to close via minimal tactic one-liner
  - L148 [soft] `skeletal-proof` in `theorem complementaryProjection_mapsTo_drazinCore` — proof appears to close via minimal tactic one-liner
  - L152 [advisory] `local-hypothesis-injection` in `theorem complementaryProjection_mapsTo_drazinCore` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L173 [soft] `skeletal-proof` in `theorem complementaryProjection_range_eq_drazinCore` — proof appears to close via minimal tactic one-liner
  - L182 [advisory] `local-hypothesis-injection` in `theorem complementaryProjection_range_eq_drazinCore` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L184 [advisory] `local-hypothesis-injection` in `theorem complementaryProjection_range_eq_drazinCore` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L186 [advisory] `local-hypothesis-injection` in `theorem complementaryProjection_range_eq_drazinCore` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L188 [advisory] `local-hypothesis-injection` in `theorem complementaryProjection_range_eq_drazinCore` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L216 [soft] `skeletal-proof` in `theorem dissipation_vanishes_on_drazinCore` — proof appears to close via minimal tactic one-liner
  - L231 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L253 [soft] `simp-law-injection` in `simp-declaration A_mul_drazinCoreProj_eq_drazinCoreProj_mul_A` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L259 [soft] `simp-law-injection` in `simp-declaration A_mul_nilpotentProj_eq_nilpotentProj_mul_A` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L265 [soft] `simp-law-injection` in `simp-declaration corePart_eq_drazinCoreProj_mul_A` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L270 [soft] `simp-law-injection` in `simp-declaration nilpotentPart_eq_nilpotentProj_mul_A` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L290 [advisory] `local-hypothesis-injection` in `def nilpotentPart` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L292 [advisory] `local-hypothesis-injection` in `def nilpotentPart` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L315 [advisory] `local-hypothesis-injection` in `def nilpotentPart` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L317 [advisory] `local-hypothesis-injection` in `def nilpotentPart` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L354 [advisory] `local-hypothesis-injection` in `def nilpotentPart` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

