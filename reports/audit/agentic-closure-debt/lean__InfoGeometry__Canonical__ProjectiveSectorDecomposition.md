# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:45.249753+00:00`
Root: `lean/InfoGeometry/Canonical/ProjectiveSectorDecomposition.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **4**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ProjectiveSectorDecomposition.lean` | `advisory` | 12 | 0 | 4 | 4 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/ProjectiveSectorDecomposition.lean`
- module: `InfoGeometry.Canonical.ProjectiveSectorDecomposition`
- status: `advisory`
- debt_score: `12`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L19 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L21 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L22 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L79 [soft] `simp-law-injection` in `simp-declaration IsStrictGradePlusRay_projectivize` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L103 [soft] `simp-law-injection` in `simp-declaration IsStrictGradeMinusRay_projectivize` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L135 [soft] `skeletal-proof` in `theorem mathlibProjectiveJ_eq_self_of_strictGradePlusRay` — proof appears to close via minimal tactic one-liner
  - L157 [soft] `skeletal-proof` in `theorem mathlibProjectiveJ_eq_self_of_strictGradeMinusRay` — proof appears to close via minimal tactic one-liner

