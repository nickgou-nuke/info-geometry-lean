# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:45.963536+00:00`
Root: `lean/InfoGeometry/Canonical/BoundedKMSErgodicWeylGWVolumeBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **6**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/BoundedKMSErgodicWeylGWVolumeBridge.lean` | `advisory` | 14 | 0 | 6 | 2 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/BoundedKMSErgodicWeylGWVolumeBridge.lean`
- module: `InfoGeometry.Canonical.BoundedKMSErgodicWeylGWVolumeBridge`
- status: `advisory`
- debt_score: `14`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L41 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L54 [soft] `law-field-locker` in `structure-field BoundedKMSErgodicWeylGWVolumeBridge.ergodicOmega` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L58 [soft] `law-field-locker` in `structure-field BoundedKMSErgodicWeylGWVolumeBridge.faceGW` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L64 [soft] `law-field-locker` in `structure-field BoundedKMSErgodicWeylGWVolumeBridge.omegaVolume_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [soft] `law-field-locker` in `structure-field BoundedKMSErgodicWeylGWVolumeBridge.phaseVolume` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L72 [soft] `law-field-locker` in `structure-field BoundedKMSErgodicWeylGWVolumeBridge.phaseVolume_flow_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L77 [soft] `law-field-locker` in `structure-field BoundedKMSErgodicWeylGWVolumeBridge.phaseVolume_renorm_invariant_of_selfSimilar` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

