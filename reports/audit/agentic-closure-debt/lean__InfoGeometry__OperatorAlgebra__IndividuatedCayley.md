# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:15.787075+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/IndividuatedCayley.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **23**
- Hard: **0**
- Soft: **16**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/IndividuatedCayley.lean` | `advisory` | 39 | 0 | 16 | 7 | 23 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/IndividuatedCayley.lean`
- module: `InfoGeometry.OperatorAlgebra.IndividuatedCayley`
- status: `advisory`
- debt_score: `39`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L44 [soft] `skeletal-proof` in `theorem self` — proof appears to close via minimal tactic one-liner
  - L66 [soft] `skeletal-proof` in `theorem sub` — proof appears to close via minimal tactic one-liner
  - L76 [soft] `skeletal-proof` in `theorem inverse_commutes_of_commutes` — proof appears to close via minimal tactic one-liner
  - L141 [soft] `law-field-locker` in `structure-field VerifiedPhaseResolvent.denom_right` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L145 [soft] `law-field-locker` in `structure-field VerifiedPhaseResolvent.denom_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L164 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L203 [advisory] `local-hypothesis-injection` in `theorem D_add_K_commutes_D_sub_K` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L204 [advisory] `local-hypothesis-injection` in `theorem D_add_K_commutes_D_sub_K` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L214 [advisory] `local-hypothesis-injection` in `theorem D_add_K_commutes_D_sub_K` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L289 [soft] `law-field-locker` in `structure-field VerifiedUnitaryResolvent.denom_right` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L293 [soft] `law-field-locker` in `structure-field VerifiedUnitaryResolvent.denom_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L301 [soft] `law-field-locker` in `structure-field VerifiedUnitaryResolvent.D_selfAdjoint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L305 [soft] `law-field-locker` in `structure-field VerifiedUnitaryResolvent.K_skewAdjoint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L345 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L368 [soft] `skeletal-proof` in `theorem boundedCayley_star_mul_self` — proof appears to close via minimal tactic one-liner
  - L396 [soft] `skeletal-proof` in `theorem boundedCayley_mul_star_self` — proof appears to close via minimal tactic one-liner
  - L461 [soft] `law-field-locker` in `structure-field VerifiedCayleyResolvent.D_selfAdjoint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L465 [soft] `law-field-locker` in `structure-field VerifiedCayleyResolvent.K_skewAdjoint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L469 [soft] `law-field-locker` in `structure-field VerifiedCayleyResolvent.D_comm_K` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L473 [soft] `law-field-locker` in `structure-field VerifiedCayleyResolvent.plus_mul_plusInv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L477 [soft] `law-field-locker` in `structure-field VerifiedCayleyResolvent.plusInv_mul_plus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L485 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

