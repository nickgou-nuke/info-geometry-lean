# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:44.019239+00:00`
Root: `lean/InfoGeometry/SuperMetriplectic/SeeleyDeWitt.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **10**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/SuperMetriplectic/SeeleyDeWitt.lean` | `advisory` | 21 | 0 | 10 | 1 | 11 |

## Findings by file

### `lean/InfoGeometry/SuperMetriplectic/SeeleyDeWitt.lean`
- module: `InfoGeometry.SuperMetriplectic.SeeleyDeWitt`
- status: `advisory`
- debt_score: `21`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [soft] `law-field-locker` in `structure-field HeatKernelZetaZeroPacket.dimensionReadout_eq_eight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L37 [soft] `law-field-locker` in `structure-field HeatKernelZetaZeroPacket.zetaZero_eq_seeleyDeWittA4` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L39 [soft] `law-field-locker` in `structure-field HeatKernelZetaZeroPacket.seeleyDeWittA4_eq_anomalyIntegral` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L84 [soft] `law-field-locker` in `structure-field SeeleyDeWittA4D4Packet.a4Density_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L114 [soft] `law-field-locker` in `structure-field PfaffianEulerIndexBridge.eulerDensity_eq_curvaturePfaffian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L116 [soft] `law-field-locker` in `structure-field PfaffianEulerIndexBridge.topologicalIndex_eq_curvaturePfaffian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L118 [soft] `law-field-locker` in `structure-field PfaffianEulerIndexBridge.topologicalIndex_eq_centralChargeRegulator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L151 [soft] `law-field-locker` in `structure-field SeeleyDeWittCasimirCapstone.heatKernel_a4_matches_density` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L153 [soft] `law-field-locker` in `structure-field SeeleyDeWittCasimirCapstone.a4_euler_matches_pfaffian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L155 [soft] `law-field-locker` in `structure-field SeeleyDeWittCasimirCapstone.pfaffian_regulator_matches_casimir` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

