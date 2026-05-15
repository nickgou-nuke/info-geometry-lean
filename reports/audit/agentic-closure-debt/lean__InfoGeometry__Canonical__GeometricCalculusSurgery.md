# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:10.719893+00:00`
Root: `lean/InfoGeometry/Canonical/GeometricCalculusSurgery.lean`
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
| `lean/InfoGeometry/Canonical/GeometricCalculusSurgery.lean` | `advisory` | 13 | 0 | 6 | 1 | 7 |

## Findings by file

### `lean/InfoGeometry/Canonical/GeometricCalculusSurgery.lean`
- module: `InfoGeometry.Canonical.GeometricCalculusSurgery`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [soft] `law-field-locker` in `structure-field BivectorPhase.isGenerator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L46 [soft] `law-field-locker` in `structure-field DirectedBoundary.directedSurfaceElement` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L65 [soft] `law-field-locker` in `structure-field CliffordResolventFamily.resolvent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L94 [soft] `vacuous-prop` in `prop <vacuous>` — Prop declaration appears to reduce to True/False
  - L111 [soft] `vacuous-prop` in `prop <vacuous>` — Prop declaration appears to reduce to True/False
  - L135 [soft] `law-field-locker` in `structure-field StokesTheoremWitness.parameterization` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

