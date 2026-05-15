# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:51.719613+00:00`
Root: `lean/InfoGeometry/Canonical/ChiralHodgeDecomposition.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **8**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ChiralHodgeDecomposition.lean` | `advisory` | 19 | 0 | 8 | 3 | 11 |

## Findings by file

### `lean/InfoGeometry/Canonical/ChiralHodgeDecomposition.lean`
- module: `InfoGeometry.Canonical.ChiralHodgeDecomposition`
- status: `advisory`
- debt_score: `19`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L33 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L35 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L72 [soft] `skeletal-proof` in `theorem rootDiracOddLane_is_spectral_odd` — proof appears to close via minimal tactic one-liner
  - L78 [soft] `simp-law-injection` in `simp-declaration modular_j_plusPoint` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L83 [soft] `simp-law-injection` in `simp-declaration modular_j_minusPoint` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L88 [soft] `simp-law-injection` in `simp-declaration spectralChiralPlusProjector_apply_minusPoint` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L94 [soft] `simp-law-injection` in `simp-declaration spectralChiralMinusProjector_apply_plusPoint` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L100 [soft] `simp-law-injection` in `simp-declaration rootDiracPlus_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L108 [soft] `simp-law-injection` in `simp-declaration rootDiracMinus_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L180 [soft] `skeletal-proof` in `theorem rootDiracOddLane_sq_eq_chiralLaplacian_sum` — proof appears to close via minimal tactic one-liner

