# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:45.802200+00:00`
Root: `lean/InfoGeometry/Canonical/ProjectorEquivariance.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **9**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ProjectorEquivariance.lean` | `advisory` | 22 | 0 | 9 | 4 | 13 |

## Findings by file

### `lean/InfoGeometry/Canonical/ProjectorEquivariance.lean`
- module: `InfoGeometry.Canonical.ProjectorEquivariance`
- status: `advisory`
- debt_score: `22`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L19 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L21 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L22 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L37 [soft] `skeletal-proof` in `theorem phaseFlow_eq_elliptic` — proof appears to close via minimal tactic one-liner
  - L52 [soft] `skeletal-proof` in `theorem chiralBoost_eq_bogoliubov` — proof appears to close via minimal tactic one-liner
  - L57 [soft] `simp-law-injection` in `simp-declaration chiralBoost_generator_sq_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L104 [soft] `simp-law-injection` in `simp-declaration plusProjector_eq_spectralPlusProj` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L109 [soft] `simp-law-injection` in `simp-declaration minusProjector_eq_spectralMinusProj` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L115 [soft] `skeletal-proof` in `theorem modularSign_eq_spectral_epsilon` — proof appears to close via minimal tactic one-liner
  - L123 [soft] `skeletal-proof` in `theorem spectral_epsilon_eq_modularSign` — proof appears to close via minimal tactic one-liner
  - L126 [soft] `simp-law-injection` in `simp-declaration modularSign_sq_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L166 [soft] `skeletal-proof` in `theorem coordinate_equivariance` — proof appears to close via minimal tactic one-liner

