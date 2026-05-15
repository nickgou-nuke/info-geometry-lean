# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:14.083463+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/FiniteJonesErlangerBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **6**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/FiniteJonesErlangerBridge.lean` | `advisory` | 17 | 0 | 6 | 5 | 11 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/FiniteJonesErlangerBridge.lean`
- module: `InfoGeometry.OperatorAlgebra.FiniteJonesErlangerBridge`
- status: `advisory`
- debt_score: `17`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L45 [soft] `law-field-locker` in `structure-field DiagonalJonesGauge.a_mul_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L48 [soft] `law-field-locker` in `structure-field DiagonalJonesGauge.b_mul_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L82 [soft] `skeletal-proof` in `theorem diagonalGauge_conjugate_diagJones` — proof appears to close via minimal tactic one-liner
  - L91 [advisory] `local-hypothesis-injection` in `theorem diagonalGauge_conjugate_diagJones` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L96 [advisory] `local-hypothesis-injection` in `theorem diagonalGauge_conjugate_diagJones` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L113 [soft] `skeletal-proof` in `theorem DiagonalJonesGauge.invMat_mul_mat` — proof appears to close via minimal tactic one-liner
  - L120 [advisory] `local-hypothesis-injection` in `theorem DiagonalJonesGauge.invMat_mul_mat` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L124 [advisory] `local-hypothesis-injection` in `theorem DiagonalJonesGauge.invMat_mul_mat` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L190 [soft] `law-field-locker` in `structure-field FiniteJonesErlangerInvariant.read` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L191 [soft] `law-field-locker` in `structure-field FiniteJonesErlangerInvariant.invariant_under_diagonal_gauge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

