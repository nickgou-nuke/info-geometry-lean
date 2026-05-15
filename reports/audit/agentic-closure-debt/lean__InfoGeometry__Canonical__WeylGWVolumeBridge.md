# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:11.869089+00:00`
Root: `lean/InfoGeometry/Canonical/WeylGWVolumeBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **30**
- Hard: **0**
- Soft: **23**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/WeylGWVolumeBridge.lean` | `advisory` | 53 | 0 | 23 | 7 | 30 |

## Findings by file

### `lean/InfoGeometry/Canonical/WeylGWVolumeBridge.lean`
- module: `InfoGeometry.Canonical.WeylGWVolumeBridge`
- status: `advisory`
- debt_score: `53`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L54 [soft] `law-field-locker` in `structure-field MirrorTwinGWCalibration.scale` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [soft] `law-field-locker` in `structure-field MirrorTwinGWCalibration.localCount` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L56 [soft] `law-field-locker` in `structure-field MirrorTwinGWCalibration.mirrorCount` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L57 [soft] `law-field-locker` in `structure-field MirrorTwinGWCalibration.twinIntensity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L77 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L80 [soft] `skeletal-proof` in `theorem localCount_apply` — proof appears to close via minimal tactic one-liner
  - L84 [soft] `skeletal-proof` in `theorem mirrorCount_apply` — proof appears to close via minimal tactic one-liner
  - L88 [soft] `skeletal-proof` in `theorem twinIntensity_apply` — proof appears to close via minimal tactic one-liner
  - L102 [soft] `law-field-locker` in `structure-field AutomorphicScaleBridge.scale` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L103 [soft] `law-field-locker` in `structure-field AutomorphicScaleBridge.gaugeScale` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L117 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L120 [soft] `skeletal-proof` in `theorem gaugeScale_apply` — proof appears to close via minimal tactic one-liner
  - L134 [soft] `law-field-locker` in `structure-field WeylGWVolumeCarrier.scale` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L135 [soft] `law-field-locker` in `structure-field WeylGWVolumeCarrier.twinIntensity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L136 [soft] `law-field-locker` in `structure-field WeylGWVolumeCarrier.gaugeScale` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L137 [soft] `law-field-locker` in `structure-field WeylGWVolumeCarrier.physicalVolume` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L166 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L169 [soft] `skeletal-proof` in `theorem physicalVolume_apply` — proof appears to close via minimal tactic one-liner
  - L216 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L219 [soft] `skeletal-proof` in `theorem projectiveCounts_apply` — proof appears to close via minimal tactic one-liner
  - L223 [soft] `skeletal-proof` in `theorem drazinGW_apply` — proof appears to close via minimal tactic one-liner
  - L227 [soft] `skeletal-proof` in `theorem volume_apply` — proof appears to close via minimal tactic one-liner
  - L278 [soft] `law-field-locker` in `structure-field PhaseVolumeRGWeylGWVolumeFusion.volumeDensity_eq_physicalReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L287 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L306 [advisory] `bridge-shaped-declaration` in `theorem volume_density_fixed_point_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L348 [soft] `law-field-locker` in `structure-field StandardFormFaceWeylGWVolumeFusion.projectiveFace` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L352 [soft] `law-field-locker` in `structure-field StandardFormFaceWeylGWVolumeFusion.omegaVolume` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L356 [soft] `law-field-locker` in `structure-field StandardFormFaceWeylGWVolumeFusion.wordToState` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L360 [soft] `law-field-locker` in `structure-field StandardFormFaceWeylGWVolumeFusion.localizedVolume_calibration` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

