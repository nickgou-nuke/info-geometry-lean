# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:44.097615+00:00`
Root: `lean/InfoGeometry/GromovWittenErlangen/ProjectiveCountChecks.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **0**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/GromovWittenErlangen/ProjectiveCountChecks.lean` | `advisory` | 7 | 0 | 0 | 7 | 7 |

## Findings by file

### `lean/InfoGeometry/GromovWittenErlangen/ProjectiveCountChecks.lean`
- module: `InfoGeometry.GromovWittenErlangen.ProjectiveCountChecks`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [advisory] `existential-packaging` in `abbrev GWCanonicalCountRayBridgeType` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L41 [advisory] `existential-packaging` in `abbrev GWProjectiveCountProbabilityBridgeType` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L47 [advisory] `existential-packaging` in `abbrev GWProjectiveCountDrazinBridgeType` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L66 [advisory] `existential-packaging` in `abbrev stateFinProbApplyToRealRef` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L72 [advisory] `existential-packaging` in `abbrev entropyAsSurprisalExpectationRef` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L85 [advisory] `existential-packaging` in `abbrev edgeResidueMulRegularInverseRef` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

