# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:45.822733+00:00`
Root: `lean/InfoGeometry/Canonical/BoundedKMSErgodicOmegaVolumeBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **6**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/BoundedKMSErgodicOmegaVolumeBridge.lean` | `advisory` | 16 | 0 | 6 | 4 | 10 |

## Findings by file

### `lean/InfoGeometry/Canonical/BoundedKMSErgodicOmegaVolumeBridge.lean`
- module: `InfoGeometry.Canonical.BoundedKMSErgodicOmegaVolumeBridge`
- status: `advisory`
- debt_score: `16`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L36 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L38 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L39 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L47 [soft] `law-field-locker` in `structure-field BoundedKMSErgodicOmegaVolumeBridge.ergodic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L50 [soft] `law-field-locker` in `structure-field BoundedKMSErgodicOmegaVolumeBridge.omegaVolume` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L54 [soft] `law-field-locker` in `structure-field BoundedKMSErgodicOmegaVolumeBridge.toVolumeOperator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L58 [soft] `law-field-locker` in `structure-field BoundedKMSErgodicOmegaVolumeBridge.fixedOperatorOfWord` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L62 [soft] `law-field-locker` in `structure-field BoundedKMSErgodicOmegaVolumeBridge.fixedOperator_selfSimilar` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [soft] `law-field-locker` in `structure-field BoundedKMSErgodicOmegaVolumeBridge.fixedOperator_volume_calibration` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

