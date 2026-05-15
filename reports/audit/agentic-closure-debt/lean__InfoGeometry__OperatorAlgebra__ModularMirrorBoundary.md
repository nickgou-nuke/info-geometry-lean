# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:18.334052+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ModularMirrorBoundary.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **7**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ModularMirrorBoundary.lean` | `advisory` | 20 | 0 | 7 | 6 | 13 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ModularMirrorBoundary.lean`
- module: `InfoGeometry.OperatorAlgebra.ModularMirrorBoundary`
- status: `advisory`
- debt_score: `20`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L59 [soft] `law-field-locker` in `structure-field ClosureMirrorBoundary.theta_input` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L189 [soft] `law-field-locker` in `structure-field MirrorBalanceLedger.quantityOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L197 [soft] `law-field-locker` in `structure-field MirrorBalanceLedger.balance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L213 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L256 [soft] `law-field-locker` in `structure-field HorizonMembraneMirror.surfaceResistance_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L265 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L306 [soft] `law-field-locker` in `structure-field UniqueTransparentLine.transparent_mem_diagonal_span` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L317 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L346 [soft] `law-field-locker` in `structure-field FluxExpulsionWitness.fluxThrough` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L349 [soft] `law-field-locker` in `structure-field FluxExpulsionWitness.flux_expelled` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L358 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

