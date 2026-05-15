# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:39.217696+00:00`
Root: `lean/InfoGeometry/Geometry/PhaseErlanger.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **9**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Geometry/PhaseErlanger.lean` | `advisory` | 20 | 0 | 9 | 2 | 11 |

## Findings by file

### `lean/InfoGeometry/Geometry/PhaseErlanger.lean`
- module: `InfoGeometry.Geometry.PhaseErlanger`
- status: `advisory`
- debt_score: `20`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L129 [soft] `skeletal-proof` in `theorem sub` — proof appears to close via minimal tactic one-liner
  - L186 [soft] `law-field-locker` in `structure-field PhaseIsomorphism.toLinear` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L187 [soft] `law-field-locker` in `structure-field PhaseIsomorphism.invLinear` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L188 [soft] `law-field-locker` in `structure-field PhaseIsomorphism.left_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L191 [soft] `law-field-locker` in `structure-field PhaseIsomorphism.right_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L270 [soft] `law-field-locker` in `structure-field ChiralAxis.chi_square_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L390 [soft] `law-field-locker` in `structure-field PhaseMetricMorphism.toLinear` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L409 [soft] `law-field-locker` in `structure-field ErlangerInvariant.read` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L410 [soft] `law-field-locker` in `structure-field ErlangerInvariant.invariant_under_phase_conjugation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L415 [advisory] `existential-packaging` in `def PhaseErlangerOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

