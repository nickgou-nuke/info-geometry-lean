# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:26.235104+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/VerifiedTrace.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **3**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/VerifiedTrace.lean` | `advisory` | 8 | 0 | 3 | 2 | 5 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/VerifiedTrace.lean`
- module: `InfoGeometry.OperatorAlgebra.VerifiedTrace`
- status: `advisory`
- debt_score: `8`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [soft] `skeletal-proof` in `theorem matrix_trace_conjugation_invariant` — proof appears to close via minimal tactic one-liner
  - L80 [soft] `law-field-locker` in `structure-field VerifiedTrace.tr` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L81 [soft] `law-field-locker` in `structure-field VerifiedTrace.invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L88 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

