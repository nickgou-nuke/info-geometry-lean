# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:54.639238+00:00`
Root: `lean/InfoGeometry/Canonical/CoarseGraining.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **4**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/CoarseGraining.lean` | `advisory` | 11 | 0 | 4 | 3 | 7 |

## Findings by file

### `lean/InfoGeometry/Canonical/CoarseGraining.lean`
- module: `InfoGeometry.Canonical.CoarseGraining`
- status: `advisory`
- debt_score: `11`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L20 [soft] `law-field-locker` in `structure-field FiniteCoarseGraining.project` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L33 [soft] `skeletal-proof` in `theorem totalWeight_eq_sum_fiberWeight` — proof appears to close via minimal tactic one-liner
  - L43 [soft] `skeletal-proof` in `theorem fiberWeight_singleton_eq_totalWeight` — proof appears to close via minimal tactic one-liner
  - L55 [advisory] `existential-packaging` in `def encoderMarginal` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L64 [advisory] `existential-packaging` in `theorem encoderMarginal_apply` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L64 [soft] `skeletal-proof` in `theorem encoderMarginal_apply` — proof appears to close via minimal tactic one-liner

