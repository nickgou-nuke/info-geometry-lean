# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:26.089272+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/VerifiedDeterminant.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **3**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/VerifiedDeterminant.lean` | `advisory` | 9 | 0 | 3 | 3 | 6 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/VerifiedDeterminant.lean`
- module: `InfoGeometry.OperatorAlgebra.VerifiedDeterminant`
- status: `advisory`
- debt_score: `9`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L33 [soft] `skeletal-proof` in `theorem matrix_det_conjugation_invariant` — proof appears to close via minimal tactic one-liner
  - L45 [advisory] `local-hypothesis-injection` in `theorem matrix_det_conjugation_invariant` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L82 [soft] `law-field-locker` in `structure-field VerifiedDeterminant.det` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L83 [soft] `law-field-locker` in `structure-field VerifiedDeterminant.invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L90 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

