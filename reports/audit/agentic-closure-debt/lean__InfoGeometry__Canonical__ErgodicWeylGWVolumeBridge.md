# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:07.341842+00:00`
Root: `lean/InfoGeometry/Canonical/ErgodicWeylGWVolumeBridge.lean`
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
| `lean/InfoGeometry/Canonical/ErgodicWeylGWVolumeBridge.lean` | `advisory` | 14 | 0 | 6 | 2 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/ErgodicWeylGWVolumeBridge.lean`
- module: `InfoGeometry.Canonical.ErgodicWeylGWVolumeBridge`
- status: `advisory`
- debt_score: `14`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L40 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L53 [soft] `law-field-locker` in `structure-field ErgodicWeylGWVolumeBridge.ergodicOmega` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L57 [soft] `law-field-locker` in `structure-field ErgodicWeylGWVolumeBridge.faceGW` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L63 [soft] `law-field-locker` in `structure-field ErgodicWeylGWVolumeBridge.omegaVolume_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [soft] `law-field-locker` in `structure-field ErgodicWeylGWVolumeBridge.phaseVolume` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L71 [soft] `law-field-locker` in `structure-field ErgodicWeylGWVolumeBridge.phaseVolume_flow_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L76 [soft] `law-field-locker` in `structure-field ErgodicWeylGWVolumeBridge.phaseVolume_renorm_invariant_of_selfSimilar` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

