# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:30.044218+00:00`
Root: `lean/InfoGeometry/Projective/Bridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **21**
- Hard: **0**
- Soft: **9**
- Advisory: **12**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Projective/Bridge.lean` | `advisory` | 30 | 0 | 9 | 12 | 21 |

## Findings by file

### `lean/InfoGeometry/Projective/Bridge.lean`
- module: `InfoGeometry.Projective.Bridge`
- status: `advisory`
- debt_score: `30`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L26 [soft] `simp-law-injection` in `simp-declaration positiveMeasureToEuclidean_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L30 [soft] `simp-law-injection` in `simp-declaration positiveMeasureToEuclidean_scale` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L64 [soft] `simp-law-injection` in `simp-declaration mem_interior_positiveOrthantCone_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L76 [soft] `simp-law-injection` in `simp-declaration interiorToPositiveMeasure_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L90 [advisory] `existential-packaging` in `def positiveMeasureEquivInterior` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L109 [advisory] `existential-packaging` in `lemma positiveMeasureToEuclidean_ne_zero` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L109 [soft] `skeletal-proof` in `lemma positiveMeasureToEuclidean_ne_zero` — proof appears to close via minimal tactic one-liner
  - L130 [soft] `skeletal-proof` in `lemma positiveMeasureToConeInteriorRay_sameRay` — proof appears to close via minimal tactic one-liner
  - L157 [advisory] `local-hypothesis-injection` in `lemma positiveMeasureToConeInteriorRay_sameRay` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L184 [soft] `simp-law-injection` in `simp-declaration projectiveClassToConeInteriorStateSpace_mk` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L188 [advisory] `existential-packaging` in `lemma projectiveClassToConeInteriorStateSpace_injective` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L211 [advisory] `local-hypothesis-injection` in `lemma projectiveClassToConeInteriorStateSpace_injective` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L214 [advisory] `local-hypothesis-injection` in `lemma projectiveClassToConeInteriorStateSpace_injective` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L215 [advisory] `local-hypothesis-injection` in `lemma projectiveClassToConeInteriorStateSpace_injective` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L217 [advisory] `local-hypothesis-injection` in `lemma projectiveClassToConeInteriorStateSpace_injective` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L220 [advisory] `local-hypothesis-injection` in `lemma projectiveClassToConeInteriorStateSpace_injective` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L223 [advisory] `local-hypothesis-injection` in `lemma projectiveClassToConeInteriorStateSpace_injective` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L225 [advisory] `local-hypothesis-injection` in `lemma projectiveClassToConeInteriorStateSpace_injective` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L274 [soft] `simp-law-injection` in `simp-declaration coneInteriorStateSpaceToProjectiveClass_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L282 [soft] `simp-law-injection` in `simp-declaration coneInteriorStateSpaceToProjectiveClass_projectiveClass` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

