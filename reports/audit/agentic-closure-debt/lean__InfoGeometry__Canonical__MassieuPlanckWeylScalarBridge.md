# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:28.016738+00:00`
Root: `lean/InfoGeometry/Canonical/MassieuPlanckWeylScalarBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **12**
- Hard: **0**
- Soft: **8**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/MassieuPlanckWeylScalarBridge.lean` | `advisory` | 20 | 0 | 8 | 4 | 12 |

## Findings by file

### `lean/InfoGeometry/Canonical/MassieuPlanckWeylScalarBridge.lean`
- module: `InfoGeometry.Canonical.MassieuPlanckWeylScalarBridge`
- status: `advisory`
- debt_score: `20`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L60 [soft] `law-field-locker` in `structure-field MassieuPlanckWeylScalarCalibration.weylScale_eq_partitionFunction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L67 [soft] `section-law-variable` in `variable B` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L107 [soft] `skeletal-proof` in `theorem totalReadout_eq_weylScalar_mul_shapeCore` — proof appears to close via minimal tactic one-liner
  - L134 [soft] `law-field-locker` in `structure-field MassieuPlanckVolumeBridge.omegaVolume` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L139 [soft] `law-field-locker` in `structure-field MassieuPlanckVolumeBridge.partitionPotential_eq_neg_modularVolumePotential_readback` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L152 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L152 [soft] `section-law-variable` in `variable B` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L202 [soft] `law-field-locker` in `structure-field MassieuPlanckBregmanBridge.bregman_partitionPotential_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L208 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L208 [soft] `section-law-variable` in `variable B` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption

