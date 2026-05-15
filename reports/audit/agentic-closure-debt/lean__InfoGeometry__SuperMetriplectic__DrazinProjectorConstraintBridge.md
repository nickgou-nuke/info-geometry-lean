# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:42.880466+00:00`
Root: `lean/InfoGeometry/SuperMetriplectic/DrazinProjectorConstraintBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **6**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/SuperMetriplectic/DrazinProjectorConstraintBridge.lean` | `advisory` | 19 | 0 | 6 | 7 | 13 |

## Findings by file

### `lean/InfoGeometry/SuperMetriplectic/DrazinProjectorConstraintBridge.lean`
- module: `InfoGeometry.SuperMetriplectic.DrazinProjectorConstraintBridge`
- status: `advisory`
- debt_score: `19`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L33 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L35 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L45 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L48 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L61 [soft] `law-field-locker` in `structure-field DrazinProjectorConstraintCompatibility.drazinCartan` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L62 [soft] `law-field-locker` in `structure-field DrazinProjectorConstraintCompatibility.triad` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L63 [soft] `law-field-locker` in `structure-field DrazinProjectorConstraintCompatibility.sameOwner` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L66 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L66 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L105 [soft] `skeletal-proof` in `theorem topologicalConstraintReadout_eq_topologicalConstraintProjector` — proof appears to close via minimal tactic one-liner
  - L111 [soft] `skeletal-proof` in `theorem topologicalConstraintProjector_readout_eq_drazin_formula` — proof appears to close via minimal tactic one-liner
  - L181 [advisory] `bridge-shaped-declaration` in `theorem drazin_projector_constraint_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

