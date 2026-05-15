# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:36.032287+00:00`
Root: `lean/InfoGeometry/Geometry/BilingualSemilinearRepresentation.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **5**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Geometry/BilingualSemilinearRepresentation.lean` | `advisory` | 13 | 0 | 5 | 3 | 8 |

## Findings by file

### `lean/InfoGeometry/Geometry/BilingualSemilinearRepresentation.lean`
- module: `InfoGeometry.Geometry.BilingualSemilinearRepresentation`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L23 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L25 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L33 [soft] `simp-law-injection` in `simp-declaration operatorSemilinear_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L34 [soft] `skeletal-proof` in `theorem operatorSemilinear_apply` — proof appears to close via minimal tactic one-liner
  - L53 [soft] `simp-law-injection` in `simp-declaration bilingualTauSemilinear_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L55 [soft] `skeletal-proof` in `theorem bilingualTauSemilinear_apply` — proof appears to close via minimal tactic one-liner
  - L74 [soft] `skeletal-proof` in `theorem operatorSemilinear_comp_apply` — proof appears to close via minimal tactic one-liner

