# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:51.793436+00:00`
Root: `lean/InfoGeometry/Canonical/RelativeModularScaleShapeSplit.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **18**
- Hard: **0**
- Soft: **1**
- Advisory: **17**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RelativeModularScaleShapeSplit.lean` | `advisory` | 19 | 0 | 1 | 17 | 18 |

## Findings by file

### `lean/InfoGeometry/Canonical/RelativeModularScaleShapeSplit.lean`
- module: `InfoGeometry.Canonical.RelativeModularScaleShapeSplit`
- status: `advisory`
- debt_score: `19`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L28 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L30 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L34 [advisory] `existential-packaging` in `def LiftedScaleShapeCompatibility` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L46 [advisory] `existential-packaging` in `theorem operatorial_scaleShapeSplit` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L69 [advisory] `local-hypothesis-injection` in `theorem drazin_quarantine_annihilates_shape` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L72 [advisory] `local-hypothesis-injection` in `theorem drazin_quarantine_annihilates_shape` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L97 [advisory] `local-hypothesis-injection` in `theorem mixed_blocks_vanish_of_commute_spectralProjector` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L137 [soft] `skeletal-proof` in `theorem relativeModular_scaleShapeSplit` — proof appears to close via minimal tactic one-liner
  - L147 [advisory] `local-hypothesis-injection` in `theorem relativeModular_scaleShapeSplit` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L150 [advisory] `local-hypothesis-injection` in `theorem relativeModular_scaleShapeSplit` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L163 [advisory] `local-hypothesis-injection` in `theorem relativeModular_scaleShapeSplit` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L165 [advisory] `local-hypothesis-injection` in `theorem relativeModular_scaleShapeSplit` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L181 [advisory] `bridge-shaped-declaration` in `theorem cp002_cp003_bridge_of_commute` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L199 [advisory] `existential-packaging` in `theorem operatorial_scaleShapeSplit_with_projectorConsequences` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L217 [advisory] `local-hypothesis-injection` in `theorem operatorial_scaleShapeSplit_with_projectorConsequences` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L221 [advisory] `local-hypothesis-injection` in `theorem operatorial_scaleShapeSplit_with_projectorConsequences` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L269 [advisory] `local-hypothesis-injection` in `theorem canonicalRelativeModularOperator_commutes_spectralProjector_of_wedgeCalibrated` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

