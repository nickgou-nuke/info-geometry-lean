# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:00.975371+00:00`
Root: `lean/InfoGeometry/Canonical/SplitCliffordHeadProjectors.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **16**
- Hard: **0**
- Soft: **15**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SplitCliffordHeadProjectors.lean` | `advisory` | 31 | 0 | 15 | 1 | 16 |

## Findings by file

### `lean/InfoGeometry/Canonical/SplitCliffordHeadProjectors.lean`
- module: `InfoGeometry.Canonical.SplitCliffordHeadProjectors`
- status: `advisory`
- debt_score: `31`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L29 [soft] `simp-law-injection` in `simp-declaration headEpsMinusProjectorTensor_eq_formula` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L34 [soft] `simp-law-injection` in `simp-declaration headEpsPlusProjectorTensor_eq_formula` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L39 [soft] `simp-law-injection` in `simp-declaration headEpsProjectorTensor_sum` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L44 [soft] `simp-law-injection` in `simp-declaration headEpsMinusProjectorTensor_mul_headEpsPlusProjectorTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L49 [soft] `simp-law-injection` in `simp-declaration headEpsPlusProjectorTensor_mul_headEpsMinusProjectorTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L54 [soft] `simp-law-injection` in `simp-declaration headEpsMinusProjectorTensor_idempotent` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L59 [soft] `simp-law-injection` in `simp-declaration headEpsPlusProjectorTensor_idempotent` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L64 [soft] `simp-law-injection` in `simp-declaration headEpsTensor_mul_headEpsMinusProjectorTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L68 [soft] `simp-law-injection` in `simp-declaration headEpsMinusProjectorTensor_mul_headEpsTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L72 [soft] `simp-law-injection` in `simp-declaration headEpsTensor_mul_headEpsPlusProjectorTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L76 [soft] `simp-law-injection` in `simp-declaration headEpsPlusProjectorTensor_mul_headEpsTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L80 [soft] `simp-law-injection` in `simp-declaration headKFlipTensor_apply_headEpsMinusProjectorTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L85 [soft] `simp-law-injection` in `simp-declaration headKFlipTensor_apply_headEpsPlusProjectorTensor` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L90 [soft] `simp-law-injection` in `simp-declaration headKFlipTensor_apply_headEpsProjectorTensor_sum` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L97 [soft] `simp-law-injection` in `simp-declaration headKFlipTensor_apply_headEpsProjectorTensor_diff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

