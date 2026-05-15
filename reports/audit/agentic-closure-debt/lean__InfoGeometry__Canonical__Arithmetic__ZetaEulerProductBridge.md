# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:39.989031+00:00`
Root: `lean/InfoGeometry/Canonical/Arithmetic/ZetaEulerProductBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **11**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/Arithmetic/ZetaEulerProductBridge.lean` | `advisory` | 24 | 0 | 11 | 2 | 13 |

## Findings by file

### `lean/InfoGeometry/Canonical/Arithmetic/ZetaEulerProductBridge.lean`
- module: `InfoGeometry.Canonical.Arithmetic.ZetaEulerProductBridge`
- status: `advisory`
- debt_score: `24`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L23 [soft] `law-field-locker` in `structure-field PrimeGasPartition.convergenceDomain` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L24 [soft] `law-field-locker` in `structure-field PrimeGasPartition.partitionFunction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L25 [soft] `law-field-locker` in `structure-field PrimeGasPartition.eulerProduct` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L32 [soft] `simp-law-injection` in `simp-declaration finiteEulerProduct_empty` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L34 [soft] `skeletal-proof` in `theorem finiteEulerProduct_empty` — proof appears to close via minimal tactic one-liner
  - L43 [soft] `simp-law-injection` in `simp-declaration finiteEulerProduct_singleton` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L45 [soft] `skeletal-proof` in `theorem finiteEulerProduct_singleton` — proof appears to close via minimal tactic one-liner
  - L57 [soft] `law-field-locker` in `structure-field AnalyticGate.re_gt_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L62 [soft] `law-field-locker` in `structure-field PrimeWeightSpecialization.partition_eq_eulerProduct` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L64 [soft] `law-field-locker` in `structure-field PrimeWeightSpecialization.eulerProduct_eq_prime_tprod` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L66 [advisory] `bridge-shaped-declaration` in `theorem zeta_euler_product_bridge` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L66 [soft] `skeletal-proof` in `theorem zeta_euler_product_bridge` — proof appears to close via minimal tactic one-liner

