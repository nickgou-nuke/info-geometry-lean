# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:45.942200+00:00`
Root: `lean/InfoGeometry/Canonical/ProjectorNoncommutativityDilationClosure.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **21**
- Hard: **0**
- Soft: **17**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ProjectorNoncommutativityDilationClosure.lean` | `advisory` | 38 | 0 | 17 | 4 | 21 |

## Findings by file

### `lean/InfoGeometry/Canonical/ProjectorNoncommutativityDilationClosure.lean`
- module: `InfoGeometry.Canonical.ProjectorNoncommutativityDilationClosure`
- status: `advisory`
- debt_score: `38`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L36 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L60 [soft] `law-field-locker` in `structure-field DilationClosureWitness.sourcedByObstruction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L62 [soft] `law-field-locker` in `structure-field DilationClosureWitness.closureContribution` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L69 [soft] `law-field-locker` in `structure-field DilationClosureVanishesWhenCommutatorZero.commutator_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L70 [soft] `law-field-locker` in `structure-field DilationClosureVanishesWhenCommutatorZero.contribution_vanishes` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L76 [soft] `law-field-locker` in `structure-field ProjectorToCl44BridgeCandidate.metricTransportWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L79 [soft] `law-field-locker` in `structure-field ProjectorToCl44BridgeCandidate.conformalClosureWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L81 [soft] `law-field-locker` in `structure-field ProjectorToCl44BridgeCandidate.cl44ReadoutWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L95 [soft] `law-field-locker` in `structure-field DrazinMPProjectorCommutator.projectorObstruction_eq_commutator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L116 [soft] `law-field-locker` in `structure-field ProjectorMismatchAnomaly.projectorObstruction_eq_chiralAnomaly` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L118 [soft] `law-field-locker` in `structure-field ProjectorMismatchAnomaly.obstructionScale_eq_norm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L143 [soft] `law-field-locker` in `structure-field DilationFromProjectorNoncommutativity.sourceWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L145 [soft] `law-field-locker` in `structure-field DilationFromProjectorNoncommutativity.obstructionScale_eq_norm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L147 [advisory] `bridge-shaped-declaration` in `def dilation_witness_of_source` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L156 [advisory] `bridge-shaped-declaration` in `theorem noncommutativity_requires_dilation_witness` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L163 [soft] `skeletal-proof` in `theorem dilation_isGZero` — proof appears to close via minimal tactic one-liner
  - L168 [soft] `skeletal-proof` in `theorem cl44_dilation_isGZero` — proof appears to close via minimal tactic one-liner
  - L185 [soft] `skeletal-proof` in `theorem closure_satisfiesKKT_TKK_Weyl_JordanLieClosure` — proof appears to close via minimal tactic one-liner
  - L200 [soft] `law-field-locker` in `structure-field Cl44ConformalReadout.readout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L207 [soft] `law-field-locker` in `structure-field SplitCl44TKKJordanLiePacket.packet` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

