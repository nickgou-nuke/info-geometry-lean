# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:37.344141+00:00`
Root: `lean/InfoGeometry/Geometry/FiniteDefectStokesModel.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **21**
- Hard: **0**
- Soft: **19**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Geometry/FiniteDefectStokesModel.lean` | `advisory` | 40 | 0 | 19 | 2 | 21 |

## Findings by file

### `lean/InfoGeometry/Geometry/FiniteDefectStokesModel.lean`
- module: `InfoGeometry.Geometry.FiniteDefectStokesModel`
- status: `advisory`
- debt_score: `40`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L45 [soft] `simp-law-injection` in `simp-declaration F_apply_zero_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L47 [soft] `skeletal-proof` in `theorem F_apply_zero_zero` — proof appears to close via minimal tactic one-liner
  - L50 [soft] `simp-law-injection` in `simp-declaration F_apply_zero_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L52 [soft] `skeletal-proof` in `theorem F_apply_zero_one` — proof appears to close via minimal tactic one-liner
  - L55 [soft] `simp-law-injection` in `simp-declaration F_apply_one_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L57 [soft] `skeletal-proof` in `theorem F_apply_one_zero` — proof appears to close via minimal tactic one-liner
  - L60 [soft] `simp-law-injection` in `simp-declaration F_apply_one_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L62 [soft] `skeletal-proof` in `theorem F_apply_one_one` — proof appears to close via minimal tactic one-liner
  - L65 [soft] `simp-law-injection` in `simp-declaration P_apply_zero_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L67 [soft] `skeletal-proof` in `theorem P_apply_zero_zero` — proof appears to close via minimal tactic one-liner
  - L70 [soft] `simp-law-injection` in `simp-declaration P_apply_zero_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L72 [soft] `skeletal-proof` in `theorem P_apply_zero_one` — proof appears to close via minimal tactic one-liner
  - L75 [soft] `simp-law-injection` in `simp-declaration P_apply_one_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L77 [soft] `skeletal-proof` in `theorem P_apply_one_zero` — proof appears to close via minimal tactic one-liner
  - L80 [soft] `simp-law-injection` in `simp-declaration P_apply_one_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L82 [soft] `skeletal-proof` in `theorem P_apply_one_one` — proof appears to close via minimal tactic one-liner
  - L141 [soft] `skeletal-proof` in `theorem geometricDerivative_ccForm_eq_defect` — proof appears to close via minimal tactic one-liner
  - L147 [soft] `skeletal-proof` in `theorem boundaryIntegral_ccForm` — proof appears to close via minimal tactic one-liner
  - L152 [soft] `skeletal-proof` in `theorem volumeIntegral_defect` — proof appears to close via minimal tactic one-liner
  - L172 [advisory] `local-hypothesis-injection` in `def defectNormalizer` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

