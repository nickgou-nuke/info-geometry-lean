# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:48.885842+00:00`
Root: `lean/InfoGeometry/Krein/BoundedKMSHestenesConnesWilsonBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **14**
- Hard: **0**
- Soft: **11**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Krein/BoundedKMSHestenesConnesWilsonBridge.lean` | `advisory` | 25 | 0 | 11 | 3 | 14 |

## Findings by file

### `lean/InfoGeometry/Krein/BoundedKMSHestenesConnesWilsonBridge.lean`
- module: `InfoGeometry.Krein.BoundedKMSHestenesConnesWilsonBridge`
- status: `advisory`
- debt_score: `25`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L31 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L33 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L61 [soft] `law-field-locker` in `structure-field BoundedKMSHestenesConnesWilsonBridge.boundedVacuum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L64 [soft] `law-field-locker` in `structure-field BoundedKMSHestenesConnesWilsonBridge.volume` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [soft] `law-field-locker` in `structure-field BoundedKMSHestenesConnesWilsonBridge.volume_omega_eq_vacuum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L72 [soft] `law-field-locker` in `structure-field BoundedKMSHestenesConnesWilsonBridge.boundedRealState_eq_volumeState` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L77 [soft] `law-field-locker` in `structure-field BoundedKMSHestenesConnesWilsonBridge.wilsonHolonomy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L80 [soft] `law-field-locker` in `structure-field BoundedKMSHestenesConnesWilsonBridge.radonNikodymLog` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L83 [soft] `law-field-locker` in `structure-field BoundedKMSHestenesConnesWilsonBridge.wilsonHolonomy_eq_radonNikodymLog` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L88 [soft] `law-field-locker` in `structure-field BoundedKMSHestenesConnesWilsonBridge.radonNikodymLog_eq_modularVolumeIncrement` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L94 [soft] `law-field-locker` in `structure-field BoundedKMSHestenesConnesWilsonBridge.connes_two_cycle_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L130 [soft] `skeletal-proof` in `theorem connesWilson_realState_eq_boundedRealState` — proof appears to close via minimal tactic one-liner
  - L138 [soft] `skeletal-proof` in `theorem connesWilson_volume_eq` — proof appears to close via minimal tactic one-liner

