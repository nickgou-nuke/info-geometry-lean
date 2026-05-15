# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:11.698770+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ConstructiveCayley.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **4**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ConstructiveCayley.lean` | `advisory` | 14 | 0 | 4 | 6 | 10 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ConstructiveCayley.lean`
- module: `InfoGeometry.OperatorAlgebra.ConstructiveCayley`
- status: `advisory`
- debt_score: `14`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L49 [soft] `skeletal-proof` in `theorem self` — proof appears to close via minimal tactic one-liner
  - L81 [soft] `skeletal-proof` in `theorem sub` — proof appears to close via minimal tactic one-liner
  - L120 [advisory] `local-hypothesis-injection` in `theorem inverse_commutes_of_commutes` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L127 [advisory] `local-hypothesis-injection` in `theorem inverse_commutes_of_commutes` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L134 [advisory] `local-hypothesis-injection` in `theorem inverse_commutes_of_commutes` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L182 [soft] `law-field-locker` in `structure-field VerifiedPhaseResolvent.denom_right` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L186 [soft] `law-field-locker` in `structure-field VerifiedPhaseResolvent.denom_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L200 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L267 [advisory] `local-hypothesis-injection` in `theorem D_sub_K_commutes_D_add_K` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

