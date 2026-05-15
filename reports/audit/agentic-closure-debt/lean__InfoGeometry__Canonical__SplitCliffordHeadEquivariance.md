# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:00.493586+00:00`
Root: `lean/InfoGeometry/Canonical/SplitCliffordHeadEquivariance.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **6**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SplitCliffordHeadEquivariance.lean` | `advisory` | 13 | 0 | 6 | 1 | 7 |

## Findings by file

### `lean/InfoGeometry/Canonical/SplitCliffordHeadEquivariance.lean`
- module: `InfoGeometry.Canonical.SplitCliffordHeadEquivariance`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L27 [soft] `simp-law-injection` in `simp-declaration headEpsProjectorTensor_diff_eq_neg_headEpsTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L34 [soft] `simp-law-injection` in `simp-declaration headKFlipResidualTensor_apply_headEpsProjectorTensor_sum` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L42 [soft] `simp-law-injection` in `simp-declaration headKFlipResidualTensor_vanishes_on_headEpsProjectorTensor_sum` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L49 [soft] `simp-law-injection` in `simp-declaration headKFlipTensor_apply_headEpsProjectorTensor_diff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L59 [soft] `simp-law-injection` in `simp-declaration headKFlipResidualTensor_apply_headEpsProjectorTensor_diff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L69 [soft] `simp-law-injection` in `simp-declaration headKFlipResidualTensor_apply_headEpsTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

