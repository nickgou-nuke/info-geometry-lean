# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:55.530030+00:00`
Root: `lean/InfoGeometry/LLM/CliffordCantorGraphRouting.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **18**
- Hard: **0**
- Soft: **13**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/LLM/CliffordCantorGraphRouting.lean` | `advisory` | 31 | 0 | 13 | 5 | 18 |

## Findings by file

### `lean/InfoGeometry/LLM/CliffordCantorGraphRouting.lean`
- module: `InfoGeometry.LLM.CliffordCantorGraphRouting`
- status: `advisory`
- debt_score: `31`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L23 [soft] `law-field-locker` in `structure-field RouterGeometry.stateNode` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L24 [soft] `law-field-locker` in `structure-field RouterGeometry.expertNode` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L25 [soft] `law-field-locker` in `structure-field RouterGeometry.graphDist` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L26 [soft] `law-field-locker` in `structure-field RouterGeometry.graphDist_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L27 [soft] `law-field-locker` in `structure-field RouterGeometry.cliffordFeature` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L28 [soft] `law-field-locker` in `structure-field RouterGeometry.expertCenter` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L29 [soft] `law-field-locker` in `structure-field RouterGeometry.cliffordSqDist` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L30 [soft] `law-field-locker` in `structure-field RouterGeometry.cliffordSqDist_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L31 [soft] `law-field-locker` in `structure-field RouterGeometry.cantorCost` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L32 [soft] `law-field-locker` in `structure-field RouterGeometry.cantorCost_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L33 [soft] `law-field-locker` in `structure-field RouterGeometry.bias` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [advisory] `existential-packaging` in `def routingScore` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L61 [advisory] `existential-packaging` in `theorem routingCost_nonneg` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L75 [advisory] `existential-packaging` in `theorem routingScore_eq_bias_sub_cost` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L128 [soft] `skeletal-proof` in `lemma routingSoftmaxWeight_sum_one` — proof appears to close via minimal tactic one-liner
  - L152 [soft] `law-field-locker` in `structure-field SparseMask.active` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L167 [advisory] `existential-packaging` in `lemma maskedRoutingWeight_nonneg` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

