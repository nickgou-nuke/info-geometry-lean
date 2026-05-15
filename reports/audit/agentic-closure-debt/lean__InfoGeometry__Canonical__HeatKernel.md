# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:13.269346+00:00`
Root: `lean/InfoGeometry/Canonical/HeatKernel.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **7**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/HeatKernel.lean` | `advisory` | 15 | 0 | 7 | 1 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/HeatKernel.lean`
- module: `InfoGeometry.Canonical.HeatKernel`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L18 [soft] `simp-law-injection` in `simp-declaration spectralLogVolume_eq_spectralBasepointLogVolume` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L38 [soft] `simp-law-injection` in `simp-declaration a0_eq_spectralLogVolume` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L49 [soft] `simp-law-injection` in `simp-declaration a1_eq_neg_spectralLogVolume` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L63 [soft] `simp-law-injection` in `simp-declaration totalScalarCurvature_eq_spinorialScalarCurvature` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L68 [soft] `simp-law-injection` in `simp-declaration totalScalarCurvature_eq_neg_six_spectralLogVolume` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L80 [soft] `simp-law-injection` in `simp-declaration einsteinHilbertAction_eq_totalScalarCurvature` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L84 [soft] `simp-law-injection` in `simp-declaration einsteinHilbertAction_eq_neg_six_spectralLogVolume` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

