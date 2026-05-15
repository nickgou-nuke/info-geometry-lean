# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:48.090473+00:00`
Root: `lean/InfoGeometry/Canonical/CantorCuntzCliffordBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **15**
- Hard: **0**
- Soft: **11**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/CantorCuntzCliffordBridge.lean` | `advisory` | 26 | 0 | 11 | 4 | 15 |

## Findings by file

### `lean/InfoGeometry/Canonical/CantorCuntzCliffordBridge.lean`
- module: `InfoGeometry.Canonical.CantorCuntzCliffordBridge`
- status: `advisory`
- debt_score: `26`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L73 [soft] `skeletal-proof` in `theorem carFromCuntz_sq_eq_zero` — proof appears to close via minimal tactic one-liner
  - L89 [soft] `skeletal-proof` in `theorem carFromCuntz_anticommutator_star_eq_one` — proof appears to close via minimal tactic one-liner
  - L113 [soft] `law-field-locker` in `structure-field CARGenerator.nilpotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L116 [soft] `law-field-locker` in `structure-field CARGenerator.car` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L135 [soft] `law-field-locker` in `structure-field CliffordPair.gamma1_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L138 [soft] `law-field-locker` in `structure-field CliffordPair.gamma2_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L141 [soft] `law-field-locker` in `structure-field CliffordPair.anticomm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L157 [soft] `law-field-locker` in `structure-field CantorCuntzCliffordSocket.car_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L198 [soft] `law-field-locker` in `structure-field CantorFierzReadout.channel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L220 [soft] `law-field-locker` in `structure-field CantorFierzAdmissible.residual` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L221 [soft] `law-field-locker` in `structure-field CantorFierzAdmissible.admissible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L235 [advisory] `bridge-shaped-declaration` in `theorem socket_car_eq_carFromCuntz` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L243 [advisory] `bridge-shaped-declaration` in `theorem socket_car_nilpotent` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L251 [advisory] `bridge-shaped-declaration` in `theorem socket_car_anticommutator` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

