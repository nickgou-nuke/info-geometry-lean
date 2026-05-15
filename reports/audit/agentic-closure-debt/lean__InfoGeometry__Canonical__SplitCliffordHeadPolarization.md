# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:00.858835+00:00`
Root: `lean/InfoGeometry/Canonical/SplitCliffordHeadPolarization.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **18**
- Hard: **0**
- Soft: **17**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SplitCliffordHeadPolarization.lean` | `advisory` | 35 | 0 | 17 | 1 | 18 |

## Findings by file

### `lean/InfoGeometry/Canonical/SplitCliffordHeadPolarization.lean`
- module: `InfoGeometry.Canonical.SplitCliffordHeadPolarization`
- status: `advisory`
- debt_score: `35`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L38 [soft] `simp-law-injection` in `simp-declaration headMinusSectorTensor_eq_formula` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L47 [soft] `simp-law-injection` in `simp-declaration headPlusSectorTensor_eq_formula` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L56 [soft] `simp-law-injection` in `simp-declaration headMinusSectorTensor_add_headPlusSectorTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L62 [soft] `simp-law-injection` in `simp-declaration headMinusSectorTensor_mul_headPlusSectorTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L75 [soft] `simp-law-injection` in `simp-declaration headPlusSectorTensor_mul_headMinusSectorTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L88 [soft] `simp-law-injection` in `simp-declaration headMinusSectorTensor_idempotent` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L102 [soft] `simp-law-injection` in `simp-declaration headPlusSectorTensor_idempotent` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L116 [soft] `simp-law-injection` in `simp-declaration headEpsTensor_mul_headNullMinusTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L121 [soft] `simp-law-injection` in `simp-declaration headNullMinusTensor_mul_headEpsTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L126 [soft] `simp-law-injection` in `simp-declaration headEpsTensor_mul_headNullPlusTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L131 [soft] `simp-law-injection` in `simp-declaration headNullPlusTensor_mul_headEpsTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L136 [soft] `simp-law-injection` in `simp-declaration headEpsTensor_mul_headMinusSectorTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L148 [soft] `simp-law-injection` in `simp-declaration headMinusSectorTensor_mul_headEpsTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L159 [soft] `simp-law-injection` in `simp-declaration headEpsTensor_mul_headPlusSectorTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L169 [soft] `simp-law-injection` in `simp-declaration headPlusSectorTensor_mul_headEpsTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L179 [soft] `simp-law-injection` in `simp-declaration headKFlipTensor_apply_headMinusSectorTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L184 [soft] `simp-law-injection` in `simp-declaration headKFlipTensor_apply_headPlusSectorTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

