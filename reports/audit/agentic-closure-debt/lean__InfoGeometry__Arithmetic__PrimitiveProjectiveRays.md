# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:33.400725+00:00`
Root: `lean/InfoGeometry/Arithmetic/PrimitiveProjectiveRays.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **3**
- Hard: **0**
- Soft: **1**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Arithmetic/PrimitiveProjectiveRays.lean` | `advisory` | 4 | 0 | 1 | 2 | 3 |

## Findings by file

### `lean/InfoGeometry/Arithmetic/PrimitiveProjectiveRays.lean`
- module: `InfoGeometry.Arithmetic.PrimitiveProjectiveRays`
- status: `advisory`
- debt_score: `4`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L76 [advisory] `existential-packaging` in `def SamePositiveRay` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L221 [soft] `law-field-locker` in `structure-field FiniteShapeScaleKLDecomposition.unnormalizedKL_eq_shape_plus_scalar` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

