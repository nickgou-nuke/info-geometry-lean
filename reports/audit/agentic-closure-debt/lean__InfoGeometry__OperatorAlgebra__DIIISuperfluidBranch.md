# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:12.739149+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/DIIISuperfluidBranch.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **8**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/DIIISuperfluidBranch.lean` | `advisory` | 19 | 0 | 8 | 3 | 11 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/DIIISuperfluidBranch.lean`
- module: `InfoGeometry.OperatorAlgebra.DIIISuperfluidBranch`
- status: `advisory`
- debt_score: `19`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L51 [soft] `law-field-locker` in `structure-field DIIISuperfluidDatum.T_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [soft] `law-field-locker` in `structure-field DIIISuperfluidDatum.C_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L59 [soft] `law-field-locker` in `structure-field DIIISuperfluidDatum.chi_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L63 [soft] `law-field-locker` in `structure-field DIIISuperfluidDatum.chi_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [soft] `law-field-locker` in `structure-field DIIISuperfluidDatum.T_commutes_H` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L71 [soft] `law-field-locker` in `structure-field DIIISuperfluidDatum.C_anticommutes_H` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L79 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L134 [soft] `law-field-locker` in `structure-field DIIICPTBranchDatum.C_T_anticomm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L146 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L240 [soft] `law-field-locker` in `structure-field DIIITopologicalInvariant.invariant_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

