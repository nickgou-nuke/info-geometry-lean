# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:35.358349+00:00`
Root: `lean/InfoGeometry/Automorphic/LFunctionResonance.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **14**
- Hard: **0**
- Soft: **8**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Automorphic/LFunctionResonance.lean` | `advisory` | 22 | 0 | 8 | 6 | 14 |

## Findings by file

### `lean/InfoGeometry/Automorphic/LFunctionResonance.lean`
- module: `InfoGeometry.Automorphic.LFunctionResonance`
- status: `advisory`
- debt_score: `22`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L47 [soft] `law-field-locker` in `structure-field AutomorphicOperatorIntertwining.bulkOp` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [soft] `law-field-locker` in `structure-field AutomorphicOperatorIntertwining.boundaryOp` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [soft] `law-field-locker` in `structure-field AutomorphicOperatorIntertwining.siegel_intertwines` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L56 [soft] `law-field-locker` in `structure-field AutomorphicOperatorIntertwining.eisenstein_intertwines` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L64 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L95 [soft] `skeletal-proof` in `theorem cuspidalProjector_commutes` — proof appears to close via minimal tactic one-liner
  - L169 [soft] `law-field-locker` in `structure-field CuspidalLFunctionDatum.Lmap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L202 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L281 [soft] `law-field-locker` in `structure-field BoundaryScatteringLFunctionDatum.Lmap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L312 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L367 [soft] `law-field-locker` in `structure-field CompatibleAutomorphicOperatorFamily.op` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L461 [advisory] `existential-packaging` in `theorem automorphicLResonanceWitness_nonempty_of_admissible` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L475 [advisory] `existential-packaging` in `def AutomorphicLResonanceOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

