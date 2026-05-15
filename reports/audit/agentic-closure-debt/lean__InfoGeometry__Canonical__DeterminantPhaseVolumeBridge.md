# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:59.536672+00:00`
Root: `lean/InfoGeometry/Canonical/DeterminantPhaseVolumeBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **3**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DeterminantPhaseVolumeBridge.lean` | `advisory` | 10 | 0 | 3 | 4 | 7 |

## Findings by file

### `lean/InfoGeometry/Canonical/DeterminantPhaseVolumeBridge.lean`
- module: `InfoGeometry.Canonical.DeterminantPhaseVolumeBridge`
- status: `advisory`
- debt_score: `10`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [soft] `law-field-locker` in `structure-field DeterminantPhaseVolumeCarrier.detReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L62 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L87 [soft] `law-field-locker` in `structure-field RenormalizationCarrier.renorm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L106 [soft] `law-field-locker` in `structure-field RenormalizedVolumeDensityCarrier.volumeDensity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L113 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L120 [advisory] `bridge-shaped-declaration` in `theorem volume_density_fixed_point_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

