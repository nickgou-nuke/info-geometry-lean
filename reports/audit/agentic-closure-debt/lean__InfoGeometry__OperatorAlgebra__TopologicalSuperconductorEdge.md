# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:25.533860+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/TopologicalSuperconductorEdge.lean`
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
| `lean/InfoGeometry/OperatorAlgebra/TopologicalSuperconductorEdge.lean` | `advisory` | 8 | 0 | 3 | 2 | 5 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/TopologicalSuperconductorEdge.lean`
- module: `InfoGeometry.OperatorAlgebra.TopologicalSuperconductorEdge`
- status: `advisory`
- debt_score: `8`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L46 [soft] `law-field-locker` in `structure-field BdGEdgeModeWitness.H` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L62 [soft] `law-field-locker` in `structure-field BdGEdgeModeWitness.edgeMode_zero_energy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L70 [soft] `law-field-locker` in `structure-field BdGEdgeModeWitness.LocalizedAt` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L92 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

