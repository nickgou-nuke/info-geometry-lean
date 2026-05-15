# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:37.163399+00:00`
Root: `lean/InfoGeometry/Bridge/RealModularBerryBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **5**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Bridge/RealModularBerryBridge.lean` | `advisory` | 12 | 0 | 5 | 2 | 7 |

## Findings by file

### `lean/InfoGeometry/Bridge/RealModularBerryBridge.lean`
- module: `InfoGeometry.Bridge.RealModularBerryBridge`
- status: `advisory`
- debt_score: `12`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L38 [soft] `law-field-locker` in `structure-field RealModularBerryBridgeData.bulkIntegral` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L41 [soft] `law-field-locker` in `structure-field RealModularBerryBridgeData.exponentiate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L50 [soft] `law-field-locker` in `structure-field RealModularBerryBridgeData.cuspRay` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L63 [soft] `law-field-locker` in `structure-field RealModularBerryBridgeData.finite_stokes_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L160 [soft] `law-field-locker` in `structure-field FiniteStokesGate.stokes_match` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L181 [advisory] `local-hypothesis-injection` in `theorem bulkInvariant_limit_eq_totalAnomaly_of_specialization` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

