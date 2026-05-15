# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:05.201589+00:00`
Root: `lean/InfoGeometry/Canonical/DrazinSum.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **22**
- Hard: **0**
- Soft: **14**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DrazinSum.lean` | `advisory` | 36 | 0 | 14 | 8 | 22 |

## Findings by file

### `lean/InfoGeometry/Canonical/DrazinSum.lean`
- module: `InfoGeometry.Canonical.DrazinSum`
- status: `advisory`
- debt_score: `36`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L28 [soft] `law-field-locker` in `structure-field DrazinPairOrthogonal.a_mul_b` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L29 [soft] `law-field-locker` in `structure-field DrazinPairOrthogonal.b_mul_a` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L30 [soft] `law-field-locker` in `structure-field DrazinPairOrthogonal.a_mul_bd` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L31 [soft] `law-field-locker` in `structure-field DrazinPairOrthogonal.bd_mul_a` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L32 [soft] `law-field-locker` in `structure-field DrazinPairOrthogonal.ad_mul_b` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L33 [soft] `law-field-locker` in `structure-field DrazinPairOrthogonal.b_mul_ad` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L34 [soft] `law-field-locker` in `structure-field DrazinPairOrthogonal.ad_mul_bd` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L35 [soft] `law-field-locker` in `structure-field DrazinPairOrthogonal.bd_mul_ad` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L95 [advisory] `local-hypothesis-injection` in `theorem orthogonal_add_pow_succ` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L97 [advisory] `local-hypothesis-injection` in `theorem orthogonal_add_pow_succ` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L150 [advisory] `local-hypothesis-injection` in `theorem orthogonal_sum_isDrazinInverse` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L165 [advisory] `local-hypothesis-injection` in `theorem orthogonal_sum_isDrazinInverse` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L167 [advisory] `local-hypothesis-injection` in `theorem orthogonal_sum_isDrazinInverse` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L207 [soft] `law-field-locker` in `structure-field GeneralizedDrazinBanachSumFormula.hypotheses` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L208 [soft] `law-field-locker` in `structure-field GeneralizedDrazinBanachSumFormula.convergenceWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L209 [soft] `law-field-locker` in `structure-field GeneralizedDrazinBanachSumFormula.generalizedDrazinInverseWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L217 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L247 [soft] `law-field-locker` in `structure-field KolihaPierceDrazinBlockPacket.regularBlockInvertibleWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L248 [soft] `law-field-locker` in `structure-field KolihaPierceDrazinBlockPacket.singularBlockQuasinilpotentWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L249 [soft] `law-field-locker` in `structure-field KolihaPierceDrazinBlockPacket.blockFormulaWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L257 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

