# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:27.811638+00:00`
Root: `lean/InfoGeometry/Optics/FiniteJonesStinespringConstructive.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **20**
- Hard: **0**
- Soft: **13**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Optics/FiniteJonesStinespringConstructive.lean` | `advisory` | 33 | 0 | 13 | 7 | 20 |

## Findings by file

### `lean/InfoGeometry/Optics/FiniteJonesStinespringConstructive.lean`
- module: `InfoGeometry.Optics.FiniteJonesStinespringConstructive`
- status: `advisory`
- debt_score: `33`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L50 [soft] `simp-law-injection` in `simp-declaration cosC` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L56 [soft] `simp-law-injection` in `simp-declaration sinC` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L71 [advisory] `local-hypothesis-injection` in `theorem cosC_star_mul_add_sinC_star_mul` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L74 [advisory] `local-hypothesis-injection` in `theorem cosC_star_mul_add_sinC_star_mul` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L80 [soft] `skeletal-proof` in `theorem scalar_defect_eq_hidden_gain` — proof appears to close via minimal tactic one-liner
  - L132 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L181 [soft] `simp-law-injection` in `simp-declaration toStinespringIsometry_R` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L183 [soft] `skeletal-proof` in `theorem toStinespringIsometry_R` — proof appears to close via minimal tactic one-liner
  - L186 [soft] `simp-law-injection` in `simp-declaration toStinespringIsometry_V` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L188 [soft] `skeletal-proof` in `theorem toStinespringIsometry_V` — proof appears to close via minimal tactic one-liner
  - L201 [soft] `skeletal-proof` in `theorem visibleDefect_eq_environmentGain` — proof appears to close via minimal tactic one-liner
  - L291 [soft] `skeletal-proof` in `theorem julia_visible_visible_block` — proof appears to close via minimal tactic one-liner
  - L301 [soft] `skeletal-proof` in `theorem julia_hidden_visible_block` — proof appears to close via minimal tactic one-liner
  - L311 [soft] `skeletal-proof` in `theorem julia_visible_hidden_block` — proof appears to close via minimal tactic one-liner
  - L321 [soft] `skeletal-proof` in `theorem julia_hidden_hidden_block` — proof appears to close via minimal tactic one-liner
  - L343 [soft] `law-field-locker` in `structure-field DefectReadout.read` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L346 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L512 [advisory] `local-hypothesis-injection` in `theorem hiddenSIntensity_le_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L520 [advisory] `local-hypothesis-injection` in `theorem hiddenPIntensity_le_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

