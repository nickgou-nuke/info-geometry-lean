# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:29.587094+00:00`
Root: `lean/InfoGeometry/Canonical/ModularKLDivergenceBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **12**
- Hard: **0**
- Soft: **4**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ModularKLDivergenceBridge.lean` | `advisory` | 16 | 0 | 4 | 8 | 12 |

## Findings by file

### `lean/InfoGeometry/Canonical/ModularKLDivergenceBridge.lean`
- module: `InfoGeometry.Canonical.ModularKLDivergenceBridge`
- status: `advisory`
- debt_score: `16`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L43 [advisory] `existential-packaging` in `theorem generalizedKL_scale_shape_split` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L43 [soft] `skeletal-proof` in `theorem generalizedKL_scale_shape_split` — proof appears to close via minimal tactic one-liner
  - L72 [advisory] `existential-packaging` in `theorem generalizedKL_scale_shape_terms_nonneg` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L99 [advisory] `existential-packaging` in `theorem generalizedKL_scale_shape_mass_term_pos_of_mass_ne` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L116 [advisory] `existential-packaging` in `theorem generalizedKL_scale_shape_split_with_nonneg` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L144 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L146 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L178 [soft] `skeletal-proof` in `theorem relativeModularScaleShapeSplit_eq_drazinActiveKernelSplit` — proof appears to close via minimal tactic one-liner
  - L300 [advisory] `existential-packaging` in `theorem relativeModular_scaleShapeSplit_eq_projectiveGaugeSplit_of_wedgeCalibrated` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L381 [soft] `simp-law-injection` in `simp-declaration positiveRay_logGenerator_eq_relativeModularPotential` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L396 [soft] `simp-law-injection` in `simp-declaration positiveRay_logGenerator_eq_neg_relativeLogDensity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

