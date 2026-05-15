# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:31.113866+00:00`
Root: `lean/InfoGeometry/Applications/STUBlackHoleQubit.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **5**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Applications/STUBlackHoleQubit.lean` | `advisory` | 12 | 0 | 5 | 2 | 7 |

## Findings by file

### `lean/InfoGeometry/Applications/STUBlackHoleQubit.lean`
- module: `InfoGeometry.Applications.STUBlackHoleQubit`
- status: `advisory`
- debt_score: `12`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L96 [soft] `law-field-locker` in `structure-field BlackHoleQubitDictionary.embedSTU` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L99 [soft] `law-field-locker` in `structure-field BlackHoleQubitDictionary.quartic_eq_hyperdeterminant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L109 [advisory] `existential-packaging` in `structure DecoherenceAsDrazinSurgery` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L125 [soft] `law-field-locker` in `structure-field DecoherenceAsDrazinSurgery.decoherence_flow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L128 [soft] `law-field-locker` in `structure-field DecoherenceAsDrazinSurgery.hits_w_state_horizon` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L133 [soft] `law-field-locker` in `structure-field DecoherenceAsDrazinSurgery.drazin_core_is_bipartite` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

