# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:41.153612+00:00`
Root: `lean/InfoGeometry/SuperMetriplectic/Axioms.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **20**
- Hard: **0**
- Soft: **19**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/SuperMetriplectic/Axioms.lean` | `advisory` | 39 | 0 | 19 | 1 | 20 |

## Findings by file

### `lean/InfoGeometry/SuperMetriplectic/Axioms.lean`
- module: `InfoGeometry.SuperMetriplectic.Axioms`
- status: `advisory`
- debt_score: `39`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L39 [soft] `law-field-locker` in `structure-field SuperchargeClosure.oddOddClosure` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L73 [soft] `law-field-locker` in `structure-field ChiralSuperchargeClosure.netOddOddClosure` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L90 [soft] `skeletal-proof` in `theorem netOddShadow_eq_right_minus_left` — proof appears to close via minimal tactic one-liner
  - L95 [soft] `skeletal-proof` in `theorem anticommutator_netOddShadow_eq_translation_add_defect` — proof appears to close via minimal tactic one-liner
  - L125 [soft] `law-field-locker` in `structure-field CartanOnsagerSplit.onsager` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L128 [soft] `law-field-locker` in `structure-field CartanOnsagerSplit.drazinCore_eq_k` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L129 [soft] `law-field-locker` in `structure-field CartanOnsagerSplit.dissipativeRange_eq_p` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L157 [soft] `law-field-locker` in `structure-field ScalarPenroseInverse.aba` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L158 [soft] `law-field-locker` in `structure-field ScalarPenroseInverse.bab` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L165 [soft] `law-field-locker` in `structure-field ScalarDrazinInverse.commute` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L166 [soft] `law-field-locker` in `structure-field ScalarDrazinInverse.reflexive` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L167 [soft] `law-field-locker` in `structure-field ScalarDrazinInverse.spectral` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L184 [soft] `law-field-locker` in `structure-field ScalarSchurDrazinBlock.penrose_matches_hidden` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L185 [soft] `law-field-locker` in `structure-field ScalarSchurDrazinBlock.drazin_matches_hidden` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L202 [soft] `skeletal-proof` in `theorem effectiveEvenOnsager_eq` — proof appears to close via minimal tactic one-liner
  - L212 [soft] `skeletal-proof` in `theorem drazinDefectProjector_eq` — proof appears to close via minimal tactic one-liner
  - L236 [soft] `law-field-locker` in `structure-field BodyEntropyProduction.production_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L237 [soft] `law-field-locker` in `structure-field BodyEntropyProduction.production_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L259 [soft] `law-field-locker` in `structure-field DrazinPenroseSchurTriad.entropy_uses_effective_block` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

