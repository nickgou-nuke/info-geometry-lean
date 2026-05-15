# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:33.003873+00:00`
Root: `lean/InfoGeometry/Canonical/NavierStokesSnapBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **23**
- Hard: **0**
- Soft: **11**
- Advisory: **12**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/NavierStokesSnapBridge.lean` | `advisory` | 34 | 0 | 11 | 12 | 23 |

## Findings by file

### `lean/InfoGeometry/Canonical/NavierStokesSnapBridge.lean`
- module: `InfoGeometry.Canonical.NavierStokesSnapBridge`
- status: `advisory`
- debt_score: `34`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L54 [soft] `law-field-locker` in `structure-field ClassicalFluidProjection.project` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L56 [soft] `law-field-locker` in `structure-field ClassicalFluidProjection.ClassicalExtreme` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L59 [soft] `law-field-locker` in `structure-field ClassicalFluidProjection.projection_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L69 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L86 [soft] `law-field-locker` in `structure-field OperatorResolutionDatum.hiddenReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L88 [soft] `law-field-locker` in `structure-field OperatorResolutionDatum.HiddenNontrivial` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L91 [soft] `law-field-locker` in `structure-field OperatorResolutionDatum.resolution_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L101 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L127 [soft] `law-field-locker` in `structure-field NavierStokesOperatorSnapBridge.projected_extreme_routes_to_hidden` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L140 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L203 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L205 [advisory] `existential-packaging` in `theorem snap_extreme_thermal_implies_tubule` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L237 [soft] `law-field-locker` in `structure-field ClassicalExtremeTubuleRouting.extreme_implies_snap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L243 [soft] `law-field-locker` in `structure-field ClassicalExtremeTubuleRouting.extreme_implies_shear` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L249 [soft] `law-field-locker` in `structure-field ClassicalExtremeTubuleRouting.extreme_implies_thermal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L265 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L267 [advisory] `existential-packaging` in `theorem classical_extreme_implies_tubule` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L309 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L347 [soft] `law-field-locker` in `structure-field NavierStokesFiveGradeResolution.extreme_detected_by_gradeTwo_memory` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L369 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L399 [advisory] `existential-packaging` in `def NavierStokesOperatorSnapBridgeOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L411 [advisory] `existential-packaging` in `def ProtectedNavierStokesSnapSectorOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

