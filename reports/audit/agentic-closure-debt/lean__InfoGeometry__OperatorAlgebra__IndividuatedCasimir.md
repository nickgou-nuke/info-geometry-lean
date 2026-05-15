# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:15.660270+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/IndividuatedCasimir.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **12**
- Hard: **0**
- Soft: **9**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/IndividuatedCasimir.lean` | `advisory` | 21 | 0 | 9 | 3 | 12 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/IndividuatedCasimir.lean`
- module: `InfoGeometry.OperatorAlgebra.IndividuatedCasimir`
- status: `advisory`
- debt_score: `21`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L51 [soft] `law-field-locker` in `structure-field InvertibleTransport.val_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [soft] `law-field-locker` in `structure-field InvertibleTransport.inv_val` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L81 [soft] `law-field-locker` in `structure-field VerifiedCasimir.central` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L87 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L88 [soft] `skeletal-proof` in `theorem fixed_by_conjugation` — proof appears to close via minimal tactic one-liner
  - L149 [soft] `law-field-locker` in `structure-field CliffordFrame.gamma` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L152 [soft] `law-field-locker` in `structure-field CliffordFrame.signature` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L155 [soft] `law-field-locker` in `structure-field CliffordFrame.gamma_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L160 [soft] `law-field-locker` in `structure-field CliffordFrame.anticomm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L173 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L191 [soft] `skeletal-proof` in `theorem quadraticCasimir_eq_scalar` — proof appears to close via minimal tactic one-liner

