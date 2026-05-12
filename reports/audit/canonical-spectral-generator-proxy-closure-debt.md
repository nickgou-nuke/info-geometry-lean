# Lean Closure Debt Crawler Report

Generated: `2026-05-11T19:07:29.216461+00:00`
Root: `lean/InfoGeometry/Canonical/SpectralGeneratorProxy.lean`

## Summary

- Files scanned: **1**
- Findings: **14**
- Hard: **0**
- Soft: **6**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SpectralGeneratorProxy.lean` | `advisory` | 20 | 0 | 6 | 8 | 14 |

## Findings by file

### `lean/InfoGeometry/Canonical/SpectralGeneratorProxy.lean`
- module: `InfoGeometry.Canonical.SpectralGeneratorProxy`
- status: `advisory`
- debt_score: `20`
- findings:
  - L47 [soft] `skeletal-proof` in `theorem axis` — proof appears to close via minimal tactic one-liner
  - L86 [soft] `skeletal-proof` in `theorem sub` — proof appears to close via minimal tactic one-liner
  - L150 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L173 [soft] `skeletal-proof` in `theorem denomInv_phase_linear` — proof appears to close via minimal tactic one-liner
  - L212 [soft] `skeletal-proof` in `theorem denominator_right_inverse` — proof appears to close via minimal tactic one-liner
  - L217 [soft] `skeletal-proof` in `theorem denominator_left_inverse` — proof appears to close via minimal tactic one-liner
  - L265 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L304 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L367 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L454 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L491 [advisory] `existential-packaging` in `def PhaseResolventOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L502 [advisory] `existential-packaging` in `def BoundedTransformOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L511 [advisory] `existential-packaging` in `def BoundedKasparovOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L541 [soft] `skeletal-proof` in `theorem boundedTransformOwnerTarget` — proof appears to close via minimal tactic one-liner

