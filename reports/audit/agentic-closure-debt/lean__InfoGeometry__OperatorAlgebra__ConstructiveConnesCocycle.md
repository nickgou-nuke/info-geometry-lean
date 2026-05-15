# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:11.826500+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ConstructiveConnesCocycle.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **6**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ConstructiveConnesCocycle.lean` | `advisory` | 13 | 0 | 6 | 1 | 7 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ConstructiveConnesCocycle.lean`
- module: `InfoGeometry.OperatorAlgebra.ConstructiveConnesCocycle`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L13 [soft] `law-field-locker` in `structure-field VerifiedModularFlow.map_mul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L14 [soft] `law-field-locker` in `structure-field VerifiedModularFlow.flow_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L15 [soft] `law-field-locker` in `structure-field VerifiedModularFlow.flow_add` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L19 [soft] `law-field-locker` in `structure-field ConnesCocycle.u` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L20 [soft] `law-field-locker` in `structure-field ConnesCocycle.cocycle_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L21 [soft] `law-field-locker` in `structure-field ConnesCocycle.intertwine_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

