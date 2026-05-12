# Lean Closure Debt Crawler Report

Generated: `2026-05-11T19:04:46.767729+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/SpectralGeneratorProxy.lean`

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
| `lean/InfoGeometry/OperatorAlgebra/SpectralGeneratorProxy.lean` | `advisory` | 16 | 0 | 4 | 8 | 12 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/SpectralGeneratorProxy.lean`
- module: `InfoGeometry.OperatorAlgebra.SpectralGeneratorProxy`
- status: `advisory`
- debt_score: `16`
- findings:
  - L60 [soft] `skeletal-proof` in `theorem self` — proof appears to close via minimal tactic one-liner
  - L92 [soft] `skeletal-proof` in `theorem sub` — proof appears to close via minimal tactic one-liner
  - L164 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L242 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L285 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L359 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L361 [soft] `skeletal-proof` in `theorem sub_mem` — proof appears to close via minimal tactic one-liner
  - L441 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L480 [advisory] `existential-packaging` in `def PhaseResolventOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L492 [advisory] `existential-packaging` in `def BoundedTransformOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L499 [advisory] `existential-packaging` in `def BoundedKasparovCycleOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L535 [soft] `skeletal-proof` in `theorem boundedTransformOwnerTarget` — proof appears to close via minimal tactic one-liner

