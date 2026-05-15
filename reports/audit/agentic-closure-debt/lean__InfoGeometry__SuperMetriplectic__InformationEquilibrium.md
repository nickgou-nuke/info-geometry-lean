# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:43.253481+00:00`
Root: `lean/InfoGeometry/SuperMetriplectic/InformationEquilibrium.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **12**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/SuperMetriplectic/InformationEquilibrium.lean` | `advisory` | 25 | 0 | 12 | 1 | 13 |

## Findings by file

### `lean/InfoGeometry/SuperMetriplectic/InformationEquilibrium.lean`
- module: `InfoGeometry.SuperMetriplectic.InformationEquilibrium`
- status: `advisory`
- debt_score: `25`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [soft] `law-field-locker` in `structure-field StabilityIndexPacket.stabilityIndex_eq_ratio_shadow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L37 [soft] `law-field-locker` in `structure-field StabilityIndexPacket.bpsBalance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L39 [soft] `law-field-locker` in `structure-field StabilityIndexPacket.drazinCore_balances_penroseShell` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L76 [soft] `law-field-locker` in `structure-field InformationalCosmologicalConstantPacket.lambdaInfo_eq_casimirResidual` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L78 [soft] `law-field-locker` in `structure-field InformationalCosmologicalConstantPacket.collapseCounterterm_eq_lambdaInfo` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L80 [soft] `law-field-locker` in `structure-field InformationalCosmologicalConstantPacket.drazinCoreSupportEnergy_eq_lambdaInfo` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L121 [soft] `law-field-locker` in `structure-field InformationEquationOfStateEquilibrium.eosDeviation_eq_bps_minus_conformal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L154 [soft] `law-field-locker` in `structure-field UniqueInformationEquilibrium.IsEquilibrium` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L157 [soft] `law-field-locker` in `structure-field UniqueInformationEquilibrium.unique_equilibrium` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L191 [soft] `law-field-locker` in `structure-field InformationEquilibriumCapstone.entropyProduction_eq_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L193 [soft] `law-field-locker` in `structure-field InformationEquilibriumCapstone.lambdaInfo_matches_casimir` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L196 [soft] `law-field-locker` in `structure-field InformationEquilibriumCapstone.lambdaInfo_matches_cosmologicalConstant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

