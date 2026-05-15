# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:15.533164+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/IndividuatedBoundedTransform.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **3**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/IndividuatedBoundedTransform.lean` | `advisory` | 8 | 0 | 3 | 2 | 5 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/IndividuatedBoundedTransform.lean`
- module: `InfoGeometry.OperatorAlgebra.IndividuatedBoundedTransform`
- status: `advisory`
- debt_score: `8`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L121 [soft] `law-field-locker` in `structure-field BoundedTransformFunctionalCalculusBridge.D_selfAdjoint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L125 [soft] `law-field-locker` in `structure-field BoundedTransformFunctionalCalculusBridge.F_is_functional_calculus_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L137 [soft] `law-field-locker` in `structure-field BoundedTransformFunctionalCalculusBridge.spectral_order_lift` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L151 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

