# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:37.204382+00:00`
Root: `lean/InfoGeometry/Geometry/ErlangerPhaseGeometry.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **12**
- Hard: **0**
- Soft: **10**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Geometry/ErlangerPhaseGeometry.lean` | `advisory` | 22 | 0 | 10 | 2 | 12 |

## Findings by file

### `lean/InfoGeometry/Geometry/ErlangerPhaseGeometry.lean`
- module: `InfoGeometry.Geometry.ErlangerPhaseGeometry`
- status: `advisory`
- debt_score: `22`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L141 [soft] `skeletal-proof` in `theorem sub` — proof appears to close via minimal tactic one-liner
  - L243 [soft] `law-field-locker` in `structure-field ErlangerInvariant.read` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L244 [soft] `law-field-locker` in `structure-field ErlangerInvariant.invariant_under_phase_conjugation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L267 [soft] `law-field-locker` in `structure-field PhaseMetricMorphism.toLinear` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L352 [advisory] `local-hypothesis-injection` in `theorem kHeightInner_preserved` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L431 [soft] `law-field-locker` in `structure-field ChiralPolarization.PL_idempotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L434 [soft] `law-field-locker` in `structure-field ChiralPolarization.PR_idempotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L436 [soft] `law-field-locker` in `structure-field ChiralPolarization.complementary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L439 [soft] `law-field-locker` in `structure-field ChiralPolarization.disjoint_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L442 [soft] `law-field-locker` in `structure-field ChiralPolarization.disjoint_right` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L454 [soft] `law-field-locker` in `structure-field PhaseChiralMorphism.toLinear` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

