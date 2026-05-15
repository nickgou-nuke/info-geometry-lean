# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:59.671382+00:00`
Root: `lean/InfoGeometry/Canonical/DiagonalMetricModularBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **30**
- Hard: **0**
- Soft: **4**
- Advisory: **26**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DiagonalMetricModularBridge.lean` | `advisory` | 34 | 0 | 4 | 26 | 30 |

## Findings by file

### `lean/InfoGeometry/Canonical/DiagonalMetricModularBridge.lean`
- module: `InfoGeometry.Canonical.DiagonalMetricModularBridge`
- status: `advisory`
- debt_score: `34`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L39 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L41 [advisory] `existential-packaging` in `def countModularData` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L51 [soft] `simp-law-injection` in `simp-declaration countModularData_modularHamiltonian_eq_relativeTomitaTakesakiOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L65 [advisory] `existential-packaging` in `def IsDiagonalRelativeCountMetricSlice` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L78 [advisory] `existential-packaging` in `theorem metricOp_eq_relativeTomitaTakesakiOp_of_isDiagonalRelativeCountMetricSlice` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L115 [advisory] `existential-packaging` in `theorem countDiagonalScalar_nonneg_of_relativeCountDensity_sum_le_card` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L115 [soft] `skeletal-proof` in `theorem countDiagonalScalar_nonneg_of_relativeCountDensity_sum_le_card` — proof appears to close via minimal tactic one-liner
  - L127 [advisory] `local-hypothesis-injection` in `theorem countDiagonalScalar_nonneg_of_relativeCountDensity_sum_le_card` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L129 [advisory] `local-hypothesis-injection` in `theorem countDiagonalScalar_nonneg_of_relativeCountDensity_sum_le_card` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L131 [advisory] `local-hypothesis-injection` in `theorem countDiagonalScalar_nonneg_of_relativeCountDensity_sum_le_card` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L132 [advisory] `local-hypothesis-injection` in `theorem countDiagonalScalar_nonneg_of_relativeCountDensity_sum_le_card` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L137 [advisory] `local-hypothesis-injection` in `theorem countDiagonalScalar_nonneg_of_relativeCountDensity_sum_le_card` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L139 [advisory] `local-hypothesis-injection` in `theorem countDiagonalScalar_nonneg_of_relativeCountDensity_sum_le_card` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L143 [advisory] `local-hypothesis-injection` in `theorem countDiagonalScalar_nonneg_of_relativeCountDensity_sum_le_card` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L151 [advisory] `local-hypothesis-injection` in `theorem countDiagonalScalar_nonneg_of_relativeCountDensity_sum_le_card` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L153 [advisory] `local-hypothesis-injection` in `theorem countDiagonalScalar_nonneg_of_relativeCountDensity_sum_le_card` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L161 [advisory] `local-hypothesis-injection` in `theorem countDiagonalScalar_nonneg_of_relativeCountDensity_sum_le_card` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L166 [advisory] `local-hypothesis-injection` in `theorem countDiagonalScalar_nonneg_of_relativeCountDensity_sum_le_card` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L169 [advisory] `local-hypothesis-injection` in `theorem countDiagonalScalar_nonneg_of_relativeCountDensity_sum_le_card` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L188 [advisory] `existential-packaging` in `def countDiagonalHessianGeometry` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L201 [advisory] `existential-packaging` in `theorem countDiagonalHessianGeometry_isDiagonalRelativeCountMetricSlice` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L219 [advisory] `existential-packaging` in `theorem countDiagonalHessianGeometry_metricOp_eq_relativeTomitaTakesakiOp` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L258 [soft] `skeletal-proof` in `theorem countDiagonalHessianGeometryOfRelativeCountDensitySumBound_metricOp_eq_relativeTomitaTakesakiOp` — proof appears to close via minimal tactic one-liner
  - L279 [advisory] `existential-packaging` in `theorem countDiagonalHessianGeometryOfRelativeCountDensitySumBound_metricOp_eq_countModularHamiltonian` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L279 [soft] `skeletal-proof` in `theorem countDiagonalHessianGeometryOfRelativeCountDensitySumBound_metricOp_eq_countModularHamiltonian` — proof appears to close via minimal tactic one-liner
  - L302 [advisory] `existential-packaging` in `theorem dirac_sq_eq_relativeTomitaTakesakiOp_of_isDiagonalRelativeCountMetricSlice` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L321 [advisory] `existential-packaging` in `theorem dirac_sq_eq_countModularHamiltonian_of_isDiagonalRelativeCountMetricSlice` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L340 [advisory] `existential-packaging` in `theorem dirac_sq_apply_eq_relativeModularHamiltonian_smul_of_isDiagonalRelativeCountMetricSlice` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L366 [advisory] `existential-packaging` in `theorem spectral_dirac_sq_eq_countModularHamiltonian_of_isDiagonalRelativeCountMetricSlice` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

