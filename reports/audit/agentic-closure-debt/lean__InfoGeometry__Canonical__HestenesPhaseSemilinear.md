# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:14.626877+00:00`
Root: `lean/InfoGeometry/Canonical/HestenesPhaseSemilinear.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **10**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/HestenesPhaseSemilinear.lean` | `advisory` | 23 | 0 | 10 | 3 | 13 |

## Findings by file

### `lean/InfoGeometry/Canonical/HestenesPhaseSemilinear.lean`
- module: `InfoGeometry.Canonical.HestenesPhaseSemilinear`
- status: `advisory`
- debt_score: `23`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L34 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L67 [soft] `simp-law-injection` in `simp-declaration sign_linear` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L69 [soft] `simp-law-injection` in `simp-declaration sign_antilinear` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L70 [soft] `simp-law-injection` in `simp-declaration comp_linear_left` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L74 [soft] `simp-law-injection` in `simp-declaration comp_linear_right` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L78 [soft] `simp-law-injection` in `simp-declaration comp_antilinear_antilinear` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L184 [soft] `skeletal-proof` in `theorem comp_isHestenesSemilinear` — proof appears to close via minimal tactic one-liner
  - L212 [soft] `skeletal-proof` in `theorem comp_antilinear_antilinear_isHestenesLinear` — proof appears to close via minimal tactic one-liner
  - L222 [soft] `skeletal-proof` in `theorem comp_linear_antilinear_isHestenesAntilinear` — proof appears to close via minimal tactic one-liner
  - L232 [soft] `skeletal-proof` in `theorem comp_antilinear_linear_isHestenesAntilinear` — proof appears to close via minimal tactic one-liner
  - L242 [soft] `skeletal-proof` in `theorem comp_linear_linear_isHestenesLinear` — proof appears to close via minimal tactic one-liner

