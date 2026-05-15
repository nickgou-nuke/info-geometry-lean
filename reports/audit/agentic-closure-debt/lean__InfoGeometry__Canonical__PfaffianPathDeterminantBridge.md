# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:41.401462+00:00`
Root: `lean/InfoGeometry/Canonical/PfaffianPathDeterminantBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **7**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/PfaffianPathDeterminantBridge.lean` | `advisory` | 16 | 0 | 7 | 2 | 9 |

## Findings by file

### `lean/InfoGeometry/Canonical/PfaffianPathDeterminantBridge.lean`
- module: `InfoGeometry.Canonical.PfaffianPathDeterminantBridge`
- status: `advisory`
- debt_score: `16`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L65 [soft] `law-field-locker` in `structure-field OrientedSourceSinkPathSystem.admissible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [soft] `law-field-locker` in `structure-field OrientedSourceSinkPathSystem.orientationSign` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [soft] `law-field-locker` in `structure-field OrientedSourceSinkPathSystem.weight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L69 [soft] `law-field-locker` in `structure-field OrientedSourceSinkPathSystem.orientationSign_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L104 [soft] `skeletal-proof` in `theorem pathDeterminantVolume_eq_pfaffian_sq` — proof appears to close via minimal tactic one-liner
  - L129 [soft] `law-field-locker` in `structure-field PfaffianPathCalibration.pfaffianReadout_eq_pathAmplitude` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L144 [soft] `law-field-locker` in `structure-field DeterminantPfaffianPathCalibration.determinantReadout_eq_pfaffian_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L180 [advisory] `existential-packaging` in `def ConnectedSourceSinkPathDeterminantTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

