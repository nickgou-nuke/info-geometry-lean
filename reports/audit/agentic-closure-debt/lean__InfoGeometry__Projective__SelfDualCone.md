# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:31.968327+00:00`
Root: `lean/InfoGeometry/Projective/SelfDualCone.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **2**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Projective/SelfDualCone.lean` | `advisory` | 7 | 0 | 2 | 3 | 5 |

## Findings by file

### `lean/InfoGeometry/Projective/SelfDualCone.lean`
- module: `InfoGeometry.Projective.SelfDualCone`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L22 [soft] `law-field-locker` in `structure-field SelfDualCone.cone` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L23 [soft] `law-field-locker` in `structure-field SelfDualCone.self_dual` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L26 [advisory] `existential-packaging` in `def ConeInteriorStateSpace` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L31 [advisory] `existential-packaging` in `def ConeBoundaryRaySpace` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

