# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:43.873541+00:00`
Root: `lean/InfoGeometry/Canonical/PrimeGasPartitions.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **10**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/PrimeGasPartitions.lean` | `advisory` | 21 | 0 | 10 | 1 | 11 |

## Findings by file

### `lean/InfoGeometry/Canonical/PrimeGasPartitions.lean`
- module: `InfoGeometry.Canonical.PrimeGasPartitions`
- status: `advisory`
- debt_score: `21`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L30 [soft] `law-field-locker` in `structure-field InfiniteEulerProductConvergenceWitness.halfPlane_Re_gt_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L37 [soft] `law-field-locker` in `structure-field InfiniteEulerProductConvergenceWitness.boson_eq_zeta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L38 [soft] `law-field-locker` in `structure-field InfiniteEulerProductConvergenceWitness.fermion_eq_zeta_div_zeta_two_beta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L39 [soft] `law-field-locker` in `structure-field InfiniteEulerProductConvergenceWitness.parity_eq_inverse_zeta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L63 [soft] `law-field-locker` in `structure-field InfiniteEulerProductWitness.halfPlane_Re_gt_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L70 [soft] `law-field-locker` in `structure-field InfiniteEulerProductWitness.boson_eq_zeta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L71 [soft] `law-field-locker` in `structure-field InfiniteEulerProductWitness.fermion_eq_zeta_div_zeta_two_beta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L72 [soft] `law-field-locker` in `structure-field InfiniteEulerProductWitness.parity_eq_inverse_zeta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L98 [soft] `law-field-locker` in `structure-field SplitPrimeSupertraceShadow.parityTrace_eq_supertraceReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L101 [soft] `simp-law-injection` in `simp-declaration parityTrace_eq_supertrace` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

