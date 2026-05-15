# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:42.807343+00:00`
Root: `lean/InfoGeometry/Canonical/PhysicsOfInformationCore.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **22**
- Hard: **0**
- Soft: **11**
- Advisory: **11**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/PhysicsOfInformationCore.lean` | `advisory` | 33 | 0 | 11 | 11 | 22 |

## Findings by file

### `lean/InfoGeometry/Canonical/PhysicsOfInformationCore.lean`
- module: `InfoGeometry.Canonical.PhysicsOfInformationCore`
- status: `advisory`
- debt_score: `33`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L40 [soft] `law-field-locker` in `structure-field PermutationPresentation.weights` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L41 [soft] `law-field-locker` in `structure-field PermutationPresentation.labels` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L50 [soft] `law-field-locker` in `structure-field CliffordPresentation.weights` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [soft] `law-field-locker` in `structure-field CliffordPresentation.labels` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L53 [soft] `law-field-locker` in `structure-field CliffordPresentation.h_semanticState` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L91 [soft] `skeletal-proof` in `theorem routingClifford_totalMass_invariant` — proof appears to close via minimal tactic one-liner
  - L110 [advisory] `bridge-shaped-declaration` in `theorem bridge_totalMass_preserved` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L110 [advisory] `placeholder-naming` in `theorem bridge_totalMass_preserved` — declaration name indicates temporary/external hypothesis surface
  - L110 [soft] `skeletal-proof` in `theorem bridge_totalMass_preserved` — proof appears to close via minimal tactic one-liner
  - L118 [advisory] `bridge-shaped-declaration` in `theorem bridge_modeEntropy_preserved` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L118 [advisory] `placeholder-naming` in `theorem bridge_modeEntropy_preserved` — declaration name indicates temporary/external hypothesis surface
  - L118 [soft] `skeletal-proof` in `theorem bridge_modeEntropy_preserved` — proof appears to close via minimal tactic one-liner
  - L126 [advisory] `bridge-shaped-declaration` in `theorem bridge_parityEntropy_preserved` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L126 [advisory] `placeholder-naming` in `theorem bridge_parityEntropy_preserved` — declaration name indicates temporary/external hypothesis surface
  - L126 [soft] `skeletal-proof` in `theorem bridge_parityEntropy_preserved` — proof appears to close via minimal tactic one-liner
  - L134 [advisory] `bridge-shaped-declaration` in `theorem bridge_semanticState_eq_canonical` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L134 [advisory] `placeholder-naming` in `theorem bridge_semanticState_eq_canonical` — declaration name indicates temporary/external hypothesis surface
  - L134 [soft] `skeletal-proof` in `theorem bridge_semanticState_eq_canonical` — proof appears to close via minimal tactic one-liner
  - L142 [advisory] `bridge-shaped-declaration` in `theorem bridge_semanticState_coord_sum_eq_totalMass` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L142 [advisory] `placeholder-naming` in `theorem bridge_semanticState_coord_sum_eq_totalMass` — declaration name indicates temporary/external hypothesis surface
  - L142 [soft] `skeletal-proof` in `theorem bridge_semanticState_coord_sum_eq_totalMass` — proof appears to close via minimal tactic one-liner

