# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:20.158550+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/OperatorialJonesCalculus.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **7**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/OperatorialJonesCalculus.lean` | `advisory` | 15 | 0 | 7 | 1 | 8 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/OperatorialJonesCalculus.lean`
- module: `InfoGeometry.OperatorAlgebra.OperatorialJonesCalculus`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L80 [soft] `law-field-locker` in `structure-field OperatorialJonesDatum.transform` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L90 [soft] `law-field-locker` in `structure-field OperatorialJonesDatum.coherence_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L193 [soft] `law-field-locker` in `structure-field JUnitaryCalibratedJonesDatum.junitary_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L216 [soft] `law-field-locker` in `structure-field BrewsterSurfaceDatum.rank_collapse_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L237 [soft] `law-field-locker` in `structure-field TotalInternalReflectionDatum.phase_retarder_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L259 [soft] `law-field-locker` in `structure-field MetalMirrorDatum.lossy_retarder_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L281 [soft] `law-field-locker` in `structure-field ChiralMediumDatum.circular_cartan_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

