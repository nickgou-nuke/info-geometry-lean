# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:36.880668+00:00`
Root: `lean/InfoGeometry/Canonical/OperatorPenroseUnification.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **18**
- Hard: **0**
- Soft: **7**
- Advisory: **11**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/OperatorPenroseUnification.lean` | `advisory` | 25 | 0 | 7 | 11 | 18 |

## Findings by file

### `lean/InfoGeometry/Canonical/OperatorPenroseUnification.lean`
- module: `InfoGeometry.Canonical.OperatorPenroseUnification`
- status: `advisory`
- debt_score: `25`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [soft] `law-field-locker` in `structure-field GeneratorPreservation.generator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L45 [soft] `law-field-locker` in `structure-field BoundaryPreservation.forward` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [soft] `law-field-locker` in `structure-field BoundaryPreservation.backward` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L54 [soft] `law-field-locker` in `structure-field CoherentClosure.act_generator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L94 [advisory] `existential-packaging` in `def RealizedProjectorTomitaIdentification` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L100 [advisory] `existential-packaging` in `def CountProjectivePolarizedAttachment` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L107 [advisory] `existential-packaging` in `def TwistedFiniteDimensionalWitness` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L113 [advisory] `existential-packaging` in `def TightenedWeylAnomalyResponse` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L120 [advisory] `existential-packaging` in `def SpinorModularIdentification` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L200 [advisory] `bridge-shaped-declaration` in `theorem junction3_twisted_finite_witness` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L297 [advisory] `existential-packaging` in `theorem operator_penrose_unification` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L314 [advisory] `existential-packaging` in `theorem operator_penrose_unification_of_capstone` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L330 [advisory] `existential-packaging` in `theorem operator_penrose_unification_closed` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L349 [soft] `law-field-locker` in `structure-field UnboundedModularTranslation.supportRestrictedLogLane` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L350 [soft] `law-field-locker` in `structure-field UnboundedModularTranslation.affiliatedGeneratorLane` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L351 [soft] `law-field-locker` in `structure-field UnboundedModularTranslation.typeIIIClosureProgram` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L357 [advisory] `existential-packaging` in `theorem boundedCapstone_seeds_unbounded_translation` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

