# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:06.771797+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ChiralLightconeStinespring.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **32**
- Hard: **0**
- Soft: **24**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ChiralLightconeStinespring.lean` | `advisory` | 56 | 0 | 24 | 8 | 32 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ChiralLightconeStinespring.lean`
- module: `InfoGeometry.OperatorAlgebra.ChiralLightconeStinespring`
- status: `advisory`
- debt_score: `56`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L40 [soft] `law-field-locker` in `structure-field ChiralProjectorPair.PL_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `law-field-locker` in `structure-field ChiralProjectorPair.PR_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L46 [soft] `law-field-locker` in `structure-field ChiralProjectorPair.complementary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [soft] `law-field-locker` in `structure-field ChiralProjectorPair.disjoint_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [soft] `law-field-locker` in `structure-field ChiralProjectorPair.disjoint_right` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L59 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L128 [soft] `law-field-locker` in `structure-field ChiralLightconeStage.mirror` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L130 [soft] `law-field-locker` in `structure-field ChiralLightconeStage.mirror_left_to_right` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L133 [soft] `law-field-locker` in `structure-field ChiralLightconeStage.mirror_right_to_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L136 [soft] `law-field-locker` in `structure-field ChiralLightconeStage.commutant_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L145 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L218 [soft] `law-field-locker` in `structure-field StinespringTomitaClinch.hidden_lands_in_commutant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L227 [soft] `law-field-locker` in `structure-field StinespringTomitaClinch.clinch_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L244 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L329 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L387 [soft] `law-field-locker` in `structure-field ChiralLightconeRouting.visibleCarrier` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L390 [soft] `law-field-locker` in `structure-field ChiralLightconeRouting.hiddenCarrier` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L393 [soft] `law-field-locker` in `structure-field ChiralLightconeRouting.left_visible_routes_to_right_hidden_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L404 [soft] `law-field-locker` in `structure-field ChiralLightconeRouting.right_visible_routes_to_left_hidden_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L431 [soft] `law-field-locker` in `structure-field LeftToRightHiddenRouting.hidden_right_of_visible_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L450 [soft] `law-field-locker` in `structure-field RightToLeftHiddenRouting.hidden_left_of_visible_right` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L491 [soft] `law-field-locker` in `structure-field ChiralLightconeStinespringClinch.tomita_cpt_calibration_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L563 [soft] `law-field-locker` in `structure-field HeatCalibration.heat` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L565 [soft] `law-field-locker` in `structure-field HeatCalibration.heat_eq_accessible_loss` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L574 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L598 [soft] `law-field-locker` in `structure-field BregmanCalibration.idealFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L600 [soft] `law-field-locker` in `structure-field BregmanCalibration.bregman` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L603 [soft] `law-field-locker` in `structure-field BregmanCalibration.bregman_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L607 [soft] `law-field-locker` in `structure-field BregmanCalibration.bregman_eq_accessible_loss` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L617 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L644 [advisory] `existential-packaging` in `def ChiralLightconeStinespringOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

