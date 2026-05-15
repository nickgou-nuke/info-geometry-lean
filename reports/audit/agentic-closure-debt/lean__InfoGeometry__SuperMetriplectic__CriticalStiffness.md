# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:42.233805+00:00`
Root: `lean/InfoGeometry/SuperMetriplectic/CriticalStiffness.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **27**
- Hard: **0**
- Soft: **24**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/SuperMetriplectic/CriticalStiffness.lean` | `advisory` | 51 | 0 | 24 | 3 | 27 |

## Findings by file

### `lean/InfoGeometry/SuperMetriplectic/CriticalStiffness.lean`
- module: `InfoGeometry.SuperMetriplectic.CriticalStiffness`
- status: `advisory`
- debt_score: `51`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L29 [soft] `law-field-locker` in `structure-field PfaffianStiffnessPacket.stiffness_eq_secondVariation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L53 [soft] `law-field-locker` in `structure-field CriticalStiffnessThreshold.criticalStiffness_eq_penroseCollapse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [soft] `law-field-locker` in `structure-field CriticalStiffnessThreshold.drazinSupport_eq_critical` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L57 [soft] `law-field-locker` in `structure-field CriticalStiffnessThreshold.stiffness_reaches_critical` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L99 [soft] `law-field-locker` in `structure-field DarkEnergyDominanceGate.darkEnergyDominates` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L100 [soft] `law-field-locker` in `structure-field DarkEnergyDominanceGate.lambdaEff_eq_casimirResidual` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L102 [soft] `law-field-locker` in `structure-field DarkEnergyDominanceGate.lambdaCritical_eq_criticalStiffness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L104 [soft] `law-field-locker` in `structure-field DarkEnergyDominanceGate.dominance_at_threshold` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L106 [soft] `law-field-locker` in `structure-field DarkEnergyDominanceGate.lambdaEff_reaches_threshold` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L144 [soft] `law-field-locker` in `structure-field WeylCasimirEffectiveActionPacket.effectiveAction_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L174 [soft] `law-field-locker` in `structure-field CasimirWeylCriticalDensityPacket.stiffness_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L178 [soft] `law-field-locker` in `structure-field CasimirWeylCriticalDensityPacket.criticalDensity_balance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L221 [advisory] `local-hypothesis-injection` in `theorem stiffness_pos_of_localDensity_lt_critical` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L241 [advisory] `local-hypothesis-injection` in `theorem stiffness_neg_of_critical_lt_localDensity` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L261 [soft] `law-field-locker` in `structure-field DarkEnergyIgnitionPacket.darkEnergyDominates` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L262 [soft] `law-field-locker` in `structure-field DarkEnergyIgnitionPacket.belowCritical` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L264 [soft] `law-field-locker` in `structure-field DarkEnergyIgnitionPacket.dominance_from_belowCritical` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L286 [soft] `law-field-locker` in `structure-field CriticalStiffnessCapstone.stiffness_matches_threshold` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L288 [soft] `law-field-locker` in `structure-field CriticalStiffnessCapstone.dominance_lambda_matches_darkEnergy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L290 [soft] `law-field-locker` in `structure-field CriticalStiffnessCapstone.dominance_casimir_matches_weylResidual` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L350 [soft] `law-field-locker` in `structure-field CasimirWeylCriticalDensityCapstone.density_stiffness_matches_threshold` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L352 [soft] `law-field-locker` in `structure-field CasimirWeylCriticalDensityCapstone.ignition_density_matches` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L355 [soft] `law-field-locker` in `structure-field CasimirWeylCriticalDensityCapstone.localDensity_eq_critical` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L416 [soft] `law-field-locker` in `structure-field CasimirWeylBelowCriticalPhaseCapstone.betaG_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L418 [soft] `law-field-locker` in `structure-field CasimirWeylBelowCriticalPhaseCapstone.strict_below_critical` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L420 [soft] `law-field-locker` in `structure-field CasimirWeylBelowCriticalPhaseCapstone.ignition_density_matches` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

