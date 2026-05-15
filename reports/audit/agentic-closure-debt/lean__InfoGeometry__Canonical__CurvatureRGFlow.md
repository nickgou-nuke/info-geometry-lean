# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:58.068114+00:00`
Root: `lean/InfoGeometry/Canonical/CurvatureRGFlow.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **0**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/CurvatureRGFlow.lean` | `advisory` | 5 | 0 | 0 | 5 | 5 |

## Findings by file

### `lean/InfoGeometry/Canonical/CurvatureRGFlow.lean`
- module: `InfoGeometry.Canonical.CurvatureRGFlow`
- status: `advisory`
- debt_score: `5`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L28 [advisory] `existential-packaging` in `theorem curvature_invariant_at_fixed_point` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L35 [advisory] `local-hypothesis-injection` in `theorem curvature_invariant_at_fixed_point` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L37 [advisory] `local-hypothesis-injection` in `theorem curvature_invariant_at_fixed_point` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L41 [advisory] `local-hypothesis-injection` in `theorem curvature_invariant_at_fixed_point` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

