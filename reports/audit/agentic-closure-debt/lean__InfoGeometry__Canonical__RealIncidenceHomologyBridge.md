# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:48.973842+00:00`
Root: `lean/InfoGeometry/Canonical/RealIncidenceHomologyBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **24**
- Hard: **0**
- Soft: **11**
- Advisory: **13**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RealIncidenceHomologyBridge.lean` | `advisory` | 35 | 0 | 11 | 13 | 24 |

## Findings by file

### `lean/InfoGeometry/Canonical/RealIncidenceHomologyBridge.lean`
- module: `InfoGeometry.Canonical.RealIncidenceHomologyBridge`
- status: `advisory`
- debt_score: `35`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L42 [soft] `law-field-locker` in `structure-field RealChainComplex.zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `law-field-locker` in `structure-field RealChainComplex.boundary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L44 [soft] `law-field-locker` in `structure-field RealChainComplex.boundary_boundary_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L48 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L58 [advisory] `existential-packaging` in `def IsBoundary` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L63 [advisory] `bridge-shaped-declaration` in `theorem boundary_boundary_zero_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L88 [soft] `law-field-locker` in `structure-field RealCochainComplex.coboundary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L89 [soft] `law-field-locker` in `structure-field RealCochainComplex.coboundary_coboundary_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L93 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L103 [advisory] `existential-packaging` in `def IsCoboundaryAtSucc` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L108 [advisory] `bridge-shaped-declaration` in `theorem coboundary_coboundary_zero_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L132 [soft] `law-field-locker` in `structure-field HestenesCoefficientModule.phase` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L133 [soft] `law-field-locker` in `structure-field HestenesCoefficientModule.phase_sq_neg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L152 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L152 [soft] `section-law-variable` in `variable sourcePhase` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L168 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L170 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L184 [advisory] `existential-packaging` in `def IsPlusChiralBoundary` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L189 [advisory] `existential-packaging` in `def IsMinusChiralBoundary` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L235 [soft] `law-field-locker` in `structure-field ChiralNilpotentComplexWitness.plus_after_minus_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L237 [soft] `law-field-locker` in `structure-field ChiralNilpotentComplexWitness.minus_after_plus_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L241 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L241 [soft] `section-law-variable` in `variable W` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption

