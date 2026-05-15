# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:43.211919+00:00`
Root: `lean/InfoGeometry/Canonical/PositiveRayCore.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **9**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/PositiveRayCore.lean` | `advisory` | 20 | 0 | 9 | 2 | 11 |

## Findings by file

### `lean/InfoGeometry/Canonical/PositiveRayCore.lean`
- module: `InfoGeometry.Canonical.PositiveRayCore`
- status: `advisory`
- debt_score: `20`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [advisory] `existential-packaging` in `abbrev PositiveOrthantRaySpace` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L51 [soft] `simp-law-injection` in `simp-declaration toConeInteriorStateSpace_ofConeInteriorStateSpace` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L56 [soft] `simp-law-injection` in `simp-declaration ofConeInteriorStateSpace_toConeInteriorStateSpace` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L66 [soft] `simp-law-injection` in `simp-declaration gaugeSection_mk` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L71 [soft] `simp-law-injection` in `simp-declaration Z_gaugeSection` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L87 [soft] `simp-law-injection` in `simp-declaration modularPotential_eq_neg_logDensity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L91 [soft] `simp-law-injection` in `simp-declaration logDensity_eq_neg_modularPotential` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L96 [soft] `simp-law-injection` in `simp-declaration exp_logDensity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L102 [soft] `simp-law-injection` in `simp-declaration gaugeSection_eq_exp_logDensity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L108 [soft] `simp-law-injection` in `simp-declaration gaugeSection_eq_exp_neg_modularPotential` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

