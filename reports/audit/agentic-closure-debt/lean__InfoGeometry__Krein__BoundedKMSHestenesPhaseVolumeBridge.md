# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:49.188808+00:00`
Root: `lean/InfoGeometry/Krein/BoundedKMSHestenesPhaseVolumeBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **8**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Krein/BoundedKMSHestenesPhaseVolumeBridge.lean` | `advisory` | 21 | 0 | 8 | 5 | 13 |

## Findings by file

### `lean/InfoGeometry/Krein/BoundedKMSHestenesPhaseVolumeBridge.lean`
- module: `InfoGeometry.Krein.BoundedKMSHestenesPhaseVolumeBridge`
- status: `advisory`
- debt_score: `21`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L31 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L33 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L65 [soft] `law-field-locker` in `structure-field BoundedKMSHestenesPhaseVolumeBridge.phaseVolume` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [soft] `law-field-locker` in `structure-field BoundedKMSHestenesPhaseVolumeBridge.detUnits` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L71 [soft] `law-field-locker` in `structure-field BoundedKMSHestenesPhaseVolumeBridge.phaseVolume_eq_detUnits_on_units` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L75 [soft] `law-field-locker` in `structure-field BoundedKMSHestenesPhaseVolumeBridge.phaseVolume_modularFlow_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L82 [soft] `law-field-locker` in `structure-field BoundedKMSHestenesPhaseVolumeBridge.phaseVolume_moebius_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L87 [soft] `law-field-locker` in `structure-field BoundedKMSHestenesPhaseVolumeBridge.phaseVolume_eq_volumeState` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L93 [soft] `law-field-locker` in `structure-field BoundedKMSHestenesPhaseVolumeBridge.determinant_channel_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L122 [advisory] `bridge-shaped-declaration` in `theorem phaseVolume_unit_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L129 [advisory] `bridge-shaped-declaration` in `theorem phaseVolume_unit_mul_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L142 [soft] `skeletal-proof` in `theorem phaseVolume_unit_one` — proof appears to close via minimal tactic one-liner

