# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:18.051594+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/MobiusClosureFixedPoints.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **26**
- Hard: **0**
- Soft: **17**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/MobiusClosureFixedPoints.lean` | `advisory` | 43 | 0 | 17 | 9 | 26 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/MobiusClosureFixedPoints.lean`
- module: `InfoGeometry.OperatorAlgebra.MobiusClosureFixedPoints`
- status: `advisory`
- debt_score: `43`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [soft] `law-field-locker` in `structure-field ClosureInvolution.theta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L36 [soft] `law-field-locker` in `structure-field ClosureInvolution.theta_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L44 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L81 [soft] `law-field-locker` in `structure-field LinearClosureInvolution.theta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L82 [soft] `law-field-locker` in `structure-field LinearClosureInvolution.theta_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L90 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L156 [soft] `law-field-locker` in `structure-field TomitaSplitInversion.observable_to_commutant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L162 [soft] `law-field-locker` in `structure-field TomitaSplitInversion.commutant_to_observable` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L172 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L229 [soft] `law-field-locker` in `structure-field OverlapScalarLaw.IsScalar` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L231 [soft] `law-field-locker` in `structure-field OverlapScalarLaw.overlap_is_scalar` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L242 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L287 [soft] `law-field-locker` in `structure-field FiveGradeMobiusInversion.negTwo_to_posTwo` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L290 [soft] `law-field-locker` in `structure-field FiveGradeMobiusInversion.posTwo_to_negTwo` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L293 [soft] `law-field-locker` in `structure-field FiveGradeMobiusInversion.negOne_to_posOne` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L296 [soft] `law-field-locker` in `structure-field FiveGradeMobiusInversion.posOne_to_negOne` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L299 [soft] `law-field-locker` in `structure-field FiveGradeMobiusInversion.zero_to_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L306 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L386 [soft] `law-field-locker` in `structure-field FiveGradeDisjointness.negOne_posOne_disjoint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L388 [soft] `law-field-locker` in `structure-field FiveGradeDisjointness.negTwo_posTwo_disjoint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L396 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L462 [soft] `law-field-locker` in `structure-field InvariantReadout.read` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L463 [soft] `law-field-locker` in `structure-field InvariantReadout.invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L471 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L519 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

