# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:19.719861+00:00`
Root: `lean/InfoGeometry/Clifford/SplitQ11Equivariance.lean`
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
| `lean/InfoGeometry/Clifford/SplitQ11Equivariance.lean` | `advisory` | 13 | 0 | 6 | 1 | 7 |

## Findings by file

### `lean/InfoGeometry/Clifford/SplitQ11Equivariance.lean`
- module: `InfoGeometry.Clifford.SplitQ11Equivariance`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L23 [soft] `simp-law-injection` in `simp-declaration phaseFlip_apply_epsProjector_sum` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L30 [soft] `simp-law-injection` in `simp-declaration phaseFlip_apply_epsProjector_diff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L41 [soft] `simp-law-injection` in `simp-declaration epsProjector_diff_eq_neg_epsGen` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L48 [soft] `simp-law-injection` in `simp-declaration phaseFlipResidual_epsProjector_sum` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L54 [soft] `simp-law-injection` in `simp-declaration phaseFlipResidual_epsProjector_diff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L62 [soft] `simp-law-injection` in `simp-declaration phaseFlipResidual_epsGen` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

