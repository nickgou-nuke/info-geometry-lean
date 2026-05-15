# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:05.590031+00:00`
Root: `lean/InfoGeometry/Canonical/ThermodynamicClosureTargets.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **0**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ThermodynamicClosureTargets.lean` | `advisory` | 6 | 0 | 0 | 6 | 6 |

## Findings by file

### `lean/InfoGeometry/Canonical/ThermodynamicClosureTargets.lean`
- module: `InfoGeometry.Canonical.ThermodynamicClosureTargets`
- status: `advisory`
- debt_score: `6`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L18 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L20 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L155 [advisory] `local-hypothesis-injection` in `theorem sinkhornStep_nonincreasing_defectAugmentedFreeEnergy_of_component_bounds` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L201 [advisory] `existential-packaging` in `def routerResidual_bounded_by_defectCentral_target` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L223 [advisory] `existential-packaging` in `def weylScale_absorbs_defect_of_scaleShapeSplit_target` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

