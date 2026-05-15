# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:02.151928+00:00`
Root: `lean/InfoGeometry/MeasureProjective.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **4**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/MeasureProjective.lean` | `advisory` | 15 | 0 | 4 | 7 | 11 |

## Findings by file

### `lean/InfoGeometry/MeasureProjective.lean`
- module: `InfoGeometry.MeasureProjective`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L19 [advisory] `existential-packaging` in `def SameRay` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L32 [advisory] `existential-packaging` in `abbrev ProjectiveState` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L35 [advisory] `existential-packaging` in `def ProjectiveState.normalize` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L44 [soft] `simp-law-injection` in `simp-declaration ProjectiveState.normalize_mk` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L49 [advisory] `existential-packaging` in `theorem self_eq_mass_smul_normalize` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L64 [advisory] `existential-packaging` in `def AEAddConst` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L94 [soft] `simp-law-injection` in `simp-declaration logPotentialClass_mk` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L120 [advisory] `existential-packaging` in `lemma logPotential_smul_right_ae` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L158 [soft] `simp-law-injection` in `simp-declaration ProjectiveState.logGenerator_mk` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L168 [soft] `simp-law-injection` in `simp-declaration ProjectiveState.logGenerator_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

