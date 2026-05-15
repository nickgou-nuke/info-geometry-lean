# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:05.847820+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/BaryonAsymmetryWitness.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **4**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/BaryonAsymmetryWitness.lean` | `advisory` | 10 | 0 | 4 | 2 | 6 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/BaryonAsymmetryWitness.lean`
- module: `InfoGeometry.OperatorAlgebra.BaryonAsymmetryWitness`
- status: `advisory`
- debt_score: `10`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [soft] `law-field-locker` in `structure-field BaryonAsymmetryAccounting.asymmetry_eq_condensateTransfer` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `law-field-locker` in `structure-field BaryonAsymmetryAccounting.baryon_number_violation_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L46 [soft] `law-field-locker` in `structure-field BaryonAsymmetryAccounting.cp_violation_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [soft] `law-field-locker` in `structure-field BaryonAsymmetryAccounting.out_of_equilibrium_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L71 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

