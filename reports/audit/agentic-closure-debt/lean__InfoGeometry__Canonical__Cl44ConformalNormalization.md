# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:53.984912+00:00`
Root: `lean/InfoGeometry/Canonical/Cl44ConformalNormalization.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **9**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/Cl44ConformalNormalization.lean` | `advisory` | 20 | 0 | 9 | 2 | 11 |

## Findings by file

### `lean/InfoGeometry/Canonical/Cl44ConformalNormalization.lean`
- module: `InfoGeometry.Canonical.Cl44ConformalNormalization`
- status: `advisory`
- debt_score: `20`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L95 [soft] `law-field-locker` in `structure-field QuadraticLightConeConformalRoute.translation_dim_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L97 [soft] `law-field-locker` in `structure-field QuadraticLightConeConformalRoute.grade_zero_dim_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L101 [soft] `law-field-locker` in `structure-field QuadraticLightConeConformalRoute.closure_dim_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L155 [soft] `law-field-locker` in `structure-field SpinFactorConformalRoute.translation_dim_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L157 [soft] `law-field-locker` in `structure-field SpinFactorConformalRoute.grade_zero_dim_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L161 [soft] `law-field-locker` in `structure-field SpinFactorConformalRoute.closure_dim_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L241 [soft] `law-field-locker` in `structure-field TrialityLeviPlacement.triality_rep_dim_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L243 [soft] `law-field-locker` in `structure-field TrialityLeviPlacement.levi_rotation_dim_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L246 [soft] `law-field-locker` in `structure-field TrialityLeviPlacement.full_conformal_dim_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L259 [advisory] `existential-packaging` in `def Cl44ConformalNormalizationOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

