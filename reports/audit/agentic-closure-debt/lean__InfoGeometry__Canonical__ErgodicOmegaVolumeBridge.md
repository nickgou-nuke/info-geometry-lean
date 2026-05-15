# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:07.230530+00:00`
Root: `lean/InfoGeometry/Canonical/ErgodicOmegaVolumeBridge.lean`
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
| `lean/InfoGeometry/Canonical/ErgodicOmegaVolumeBridge.lean` | `advisory` | 16 | 0 | 6 | 4 | 10 |

## Findings by file

### `lean/InfoGeometry/Canonical/ErgodicOmegaVolumeBridge.lean`
- module: `InfoGeometry.Canonical.ErgodicOmegaVolumeBridge`
- status: `advisory`
- debt_score: `16`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L38 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L40 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L41 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L53 [soft] `law-field-locker` in `structure-field ErgodicOmegaVolumeBridge.ergodic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L56 [soft] `law-field-locker` in `structure-field ErgodicOmegaVolumeBridge.omegaVolume` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L60 [soft] `law-field-locker` in `structure-field ErgodicOmegaVolumeBridge.toVolumeOperator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L64 [soft] `law-field-locker` in `structure-field ErgodicOmegaVolumeBridge.fixedOperatorOfWord` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [soft] `law-field-locker` in `structure-field ErgodicOmegaVolumeBridge.fixedOperator_selfSimilar` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L74 [soft] `law-field-locker` in `structure-field ErgodicOmegaVolumeBridge.fixedOperator_volume_calibration` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

