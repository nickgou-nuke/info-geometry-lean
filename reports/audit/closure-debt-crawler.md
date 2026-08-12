# Lean Closure Debt Crawler Report

Generated: `2026-08-09T20:42:33.190748+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/BianchiOperatorLift.lean`
Authority tier: `heuristic-proxy`

## Summary

- Files scanned: **1**
- Findings: **3**
- Hard: **0**
- Soft: **3**
- Advisory: **0**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/BianchiOperatorLift.lean` | `advisory` | 6 | 0 | 3 | 0 | 3 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/BianchiOperatorLift.lean`
- module: `InfoGeometry.OperatorAlgebra.BianchiOperatorLift`
- status: `advisory`
- debt_score: `6`
- findings:
  - L15 [soft] `law-field-locker` in `structure-field AlgebraicBianchiData.first_bianchi` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L15 [soft] `uninstantiated-law-locker` in `structure AlgebraicBianchiData` — structure/class has theorem-like fields but no visible constructor site (`.mk`, `: Name :=`, or `: Name where`) in the scanned root; this may be a proof-debt locker rather than implemented mathematics
  - L16 [soft] `law-field-locker` in `structure-field AlgebraicBianchiData.second_bianchi` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

