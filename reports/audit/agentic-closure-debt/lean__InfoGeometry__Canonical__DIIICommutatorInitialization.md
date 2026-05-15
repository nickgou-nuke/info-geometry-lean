# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:58.205420+00:00`
Root: `lean/InfoGeometry/Canonical/DIIICommutatorInitialization.lean`
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
| `lean/InfoGeometry/Canonical/DIIICommutatorInitialization.lean` | `advisory` | 22 | 0 | 8 | 6 | 14 |

## Findings by file

### `lean/InfoGeometry/Canonical/DIIICommutatorInitialization.lean`
- module: `InfoGeometry.Canonical.DIIICommutatorInitialization`
- status: `advisory`
- debt_score: `22`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L31 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L33 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L42 [advisory] `existential-packaging` in `class TopologicalClassDIII` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L50 [soft] `law-field-locker` in `class-field TopologicalClassDIII.T_squared` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [soft] `law-field-locker` in `class-field TopologicalClassDIII.P_squared` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [soft] `law-field-locker` in `class-field TopologicalClassDIII.T_commutes` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L53 [soft] `law-field-locker` in `class-field TopologicalClassDIII.P_anticommutes` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L54 [soft] `law-field-locker` in `class-field TopologicalClassDIII.C_definition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L58 [soft] `skeletal-proof` in `theorem commutator_T_H_eq_zero` — proof appears to close via minimal tactic one-liner
  - L79 [advisory] `bridge-shaped-declaration` in `theorem chiral_witness_exists` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L79 [advisory] `existential-packaging` in `theorem chiral_witness_exists` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L90 [soft] `skeletal-proof` in `theorem topologicalClassDIII_of_commutation_data` — proof appears to close via minimal tactic one-liner
  - L122 [soft] `skeletal-proof` in `theorem topologicalClassDIII_of_realBdGDatum` — proof appears to close via minimal tactic one-liner

