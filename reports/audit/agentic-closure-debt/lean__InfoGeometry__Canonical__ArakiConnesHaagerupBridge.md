# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:39.873479+00:00`
Root: `lean/InfoGeometry/Canonical/ArakiConnesHaagerupBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **18**
- Hard: **0**
- Soft: **11**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ArakiConnesHaagerupBridge.lean` | `advisory` | 29 | 0 | 11 | 7 | 18 |

## Findings by file

### `lean/InfoGeometry/Canonical/ArakiConnesHaagerupBridge.lean`
- module: `InfoGeometry.Canonical.ArakiConnesHaagerupBridge`
- status: `advisory`
- debt_score: `29`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L40 [soft] `law-field-locker` in `structure-field ArakiConnesHaagerupTriad.connesCocycle` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L44 [soft] `law-field-locker` in `structure-field ArakiConnesHaagerupTriad.arakiRelativeEntropy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L48 [soft] `law-field-locker` in `structure-field ArakiConnesHaagerupTriad.toCore` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [soft] `law-field-locker` in `structure-field ArakiConnesHaagerupTriad.coreWeight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L56 [soft] `law-field-locker` in `structure-field ArakiConnesHaagerupTriad.entropy_cocycle_compatibility` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L62 [soft] `law-field-locker` in `structure-field ArakiConnesHaagerupTriad.cone_core_compatibility` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L72 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L95 [advisory] `bridge-shaped-declaration` in `theorem cone_self_dual_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L101 [advisory] `bridge-shaped-declaration` in `theorem entropy_cocycle_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L107 [advisory] `bridge-shaped-declaration` in `theorem cone_core_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L127 [soft] `law-field-locker` in `structure-field StandardFormCantorConeSystem.cylinderProjection` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L131 [soft] `law-field-locker` in `structure-field StandardFormCantorConeSystem.reflectedCylinder` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L135 [soft] `law-field-locker` in `structure-field StandardFormCantorConeSystem.referenceWeight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L139 [soft] `law-field-locker` in `structure-field StandardFormCantorConeSystem.referenceWeight_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L143 [soft] `law-field-locker` in `structure-field StandardFormCantorConeSystem.reflectedCylinder_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L153 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L176 [advisory] `bridge-shaped-declaration` in `theorem reflectedCylinder_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

