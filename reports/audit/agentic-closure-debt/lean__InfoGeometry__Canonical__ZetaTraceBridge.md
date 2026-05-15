# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:14.986332+00:00`
Root: `lean/InfoGeometry/Canonical/ZetaTraceBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **6**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ZetaTraceBridge.lean` | `advisory` | 14 | 0 | 6 | 2 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/ZetaTraceBridge.lean`
- module: `InfoGeometry.Canonical.ZetaTraceBridge`
- status: `advisory`
- debt_score: `14`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L11 [soft] `law-field-locker` in `structure-field PrimeGasPartition.convergenceDomain` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L12 [soft] `law-field-locker` in `structure-field PrimeGasPartition.partitionFunction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L13 [soft] `law-field-locker` in `structure-field PrimeGasPartition.eulerProduct` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L20 [soft] `law-field-locker` in `structure-field PrimeWeightSpecialization.partition_eq_eulerProduct` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L22 [soft] `law-field-locker` in `structure-field PrimeWeightSpecialization.eulerProduct_eq_prime_tprod` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L24 [advisory] `bridge-shaped-declaration` in `theorem zeta_trace_bridge` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L24 [soft] `skeletal-proof` in `theorem zeta_trace_bridge` — proof appears to close via minimal tactic one-liner

