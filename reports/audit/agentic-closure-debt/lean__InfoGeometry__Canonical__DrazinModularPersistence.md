# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:04.120255+00:00`
Root: `lean/InfoGeometry/Canonical/DrazinModularPersistence.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **15**
- Hard: **0**
- Soft: **10**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DrazinModularPersistence.lean` | `advisory` | 25 | 0 | 10 | 5 | 15 |

## Findings by file

### `lean/InfoGeometry/Canonical/DrazinModularPersistence.lean`
- module: `InfoGeometry.Canonical.DrazinModularPersistence`
- status: `advisory`
- debt_score: `25`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L53 [soft] `law-field-locker` in `structure-field DrazinSupportData.p_def` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L54 [soft] `law-field-locker` in `structure-field DrazinSupportData.p_self_adjoint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L59 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L223 [soft] `law-field-locker` in `structure-field RealExpectationState.expect` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L224 [soft] `law-field-locker` in `structure-field RealExpectationState.unital` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L225 [soft] `law-field-locker` in `structure-field RealExpectationState.positivity_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L284 [advisory] `existential-packaging` in `theorem invertible_transport` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L350 [soft] `law-field-locker` in `structure-field FlowInvariantRealExpectationState.flow_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L357 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L391 [soft] `law-field-locker` in `structure-field FierzChannelMap.channel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L396 [soft] `law-field-locker` in `structure-field FierzCoordinates.coord` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L401 [soft] `law-field-locker` in `structure-field FierzResidual.residual` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L436 [soft] `law-field-locker` in `structure-field HorizonFierzCompatibilityAssumption.compatibility_assumption` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L450 [advisory] `bridge-shaped-declaration` in `theorem fierz_quadric_from_modular_physical_horizon_assumption` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

