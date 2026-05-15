# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:40.120224+00:00`
Root: `lean/InfoGeometry/Canonical/ArnoldApproximationCore.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **8**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ArnoldApproximationCore.lean` | `advisory` | 18 | 0 | 8 | 2 | 10 |

## Findings by file

### `lean/InfoGeometry/Canonical/ArnoldApproximationCore.lean`
- module: `InfoGeometry.Canonical.ArnoldApproximationCore`
- status: `advisory`
- debt_score: `18`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L31 [soft] `law-field-locker` in `structure-field ArnoldShapeScaleCost.shapeTerm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L32 [soft] `law-field-locker` in `structure-field ArnoldShapeScaleCost.scaleTerm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L33 [soft] `law-field-locker` in `structure-field ArnoldShapeScaleCost.shape_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L34 [soft] `law-field-locker` in `structure-field ArnoldShapeScaleCost.scale_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L65 [soft] `law-field-locker` in `structure-field ArnoldGeneratorApproximationContract.target` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L66 [soft] `law-field-locker` in `structure-field ArnoldGeneratorApproximationContract.costModel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L69 [soft] `law-field-locker` in `structure-field ArnoldGeneratorApproximationContract.costBound_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L70 [soft] `law-field-locker` in `structure-field ArnoldGeneratorApproximationContract.pointwise_cost_le` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L133 [advisory] `existential-packaging` in `def HasArnoldApproximationAt` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

