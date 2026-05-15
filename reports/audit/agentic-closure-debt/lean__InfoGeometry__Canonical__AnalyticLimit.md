# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:38.728707+00:00`
Root: `lean/InfoGeometry/Canonical/AnalyticLimit.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **5**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/AnalyticLimit.lean` | `advisory` | 11 | 0 | 5 | 1 | 6 |

## Findings by file

### `lean/InfoGeometry/Canonical/AnalyticLimit.lean`
- module: `InfoGeometry.Canonical.AnalyticLimit`
- status: `advisory`
- debt_score: `11`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L23 [soft] `law-field-locker` in `structure-field FinitePrimeCutoffDirichletData.finiteEuler_eq_dirichlet` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L36 [soft] `skeletal-proof` in `theorem finiteInverseZeta_eq_finiteEulerProduct` — proof appears to close via minimal tactic one-liner
  - L50 [soft] `law-field-locker` in `structure-field AnalyticLimitWitness.beta_gt_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [soft] `law-field-locker` in `structure-field AnalyticLimitWitness.limitStatement` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L53 [soft] `law-field-locker` in `structure-field AnalyticLimitWitness.inverseZeta_eq_limit` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

