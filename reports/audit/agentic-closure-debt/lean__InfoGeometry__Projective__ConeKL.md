# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:30.172884+00:00`
Root: `lean/InfoGeometry/Projective/ConeKL.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **14**
- Hard: **0**
- Soft: **10**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Projective/ConeKL.lean` | `advisory` | 24 | 0 | 10 | 4 | 14 |

## Findings by file

### `lean/InfoGeometry/Projective/ConeKL.lean`
- module: `InfoGeometry.Projective.ConeKL`
- status: `advisory`
- debt_score: `24`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L38 [soft] `simp-law-injection` in `simp-declaration klLikeOnProj_mk` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L47 [soft] `simp-law-injection` in `simp-declaration generalizedKLOnProj_mk` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L56 [soft] `simp-law-injection` in `simp-declaration generalizedKLOnProj_eq_klLikeOnProj` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L79 [advisory] `local-hypothesis-injection` in `lemma klLikeOnProj_nonneg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L81 [soft] `skeletal-proof` in `lemma generalizedKL_projective_radial_decomposition_onProj` — proof appears to close via minimal tactic one-liner
  - L108 [soft] `simp-law-injection` in `simp-declaration klLikeOnConeInteriorStateSpace_projectiveClass` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L117 [soft] `simp-law-injection` in `simp-declaration generalizedKLOnConeInteriorStateSpace_projectiveClass` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L127 [soft] `simp-law-injection` in `simp-declaration generalizedKLOnConeInteriorStateSpace_eq_klLikeOnConeInteriorStateSpace` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L171 [advisory] `existential-packaging` in `lemma klLikeOnConeInteriorStateSpace_nonneg` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L176 [advisory] `local-hypothesis-injection` in `lemma klLikeOnConeInteriorStateSpace_nonneg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L211 [soft] `simp-law-injection` in `simp-declaration klLikeOnProj_mk` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L221 [soft] `simp-law-injection` in `simp-declaration generalizedKLOnProj_mk` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L231 [soft] `simp-law-injection` in `simp-declaration generalizedKLOnProj_eq_klLikeOnProj` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

