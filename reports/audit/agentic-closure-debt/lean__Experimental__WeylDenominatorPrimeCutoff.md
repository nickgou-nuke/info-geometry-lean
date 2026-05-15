# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:27.209908+00:00`
Root: `lean/Experimental/WeylDenominatorPrimeCutoff.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **24**
- Hard: **0**
- Soft: **23**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/Experimental/WeylDenominatorPrimeCutoff.lean` | `advisory` | 47 | 0 | 23 | 1 | 24 |

## Findings by file

### `lean/Experimental/WeylDenominatorPrimeCutoff.lean`
- module: `Experimental.WeylDenominatorPrimeCutoff`
- status: `advisory`
- debt_score: `47`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L20 [soft] `law-field-locker` in `structure-field PrimeGasPartition.prime` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L21 [soft] `law-field-locker` in `structure-field PrimeGasPartition.prime_isPrime` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L22 [soft] `law-field-locker` in `structure-field PrimeGasPartition.energyOfPrime` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L23 [soft] `law-field-locker` in `structure-field PrimeGasPartition.convergenceDomain` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L24 [soft] `law-field-locker` in `structure-field PrimeGasPartition.partitionFunction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L25 [soft] `law-field-locker` in `structure-field PrimeGasPartition.eulerProduct` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L32 [soft] `simp-law-injection` in `simp-declaration primeEnergy_eq_energyOfPrime` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L34 [soft] `skeletal-proof` in `lemma primeEnergy_eq_energyOfPrime` — proof appears to close via minimal tactic one-liner
  - L41 [soft] `simp-law-injection` in `simp-declaration finiteEulerProduct_empty` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L55 [soft] `simp-law-injection` in `simp-declaration finiteEulerProduct_singleton` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L65 [soft] `law-field-locker` in `structure-field AnalyticGate.re_gt_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L82 [soft] `law-field-locker` in `structure-field PrimeWeightSpecialization.support_eq_univ` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L83 [soft] `law-field-locker` in `structure-field PrimeWeightSpecialization.partitionFunction_eq_tprod` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L87 [soft] `law-field-locker` in `structure-field PrimeWeightSpecialization.eulerProduct_eq_tprod` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L127 [soft] `simp-law-injection` in `simp-declaration zetaPrimeGas_energyOfPrime` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L129 [soft] `skeletal-proof` in `lemma zetaPrimeGas_energyOfPrime` — proof appears to close via minimal tactic one-liner
  - L131 [soft] `simp-law-injection` in `simp-declaration zetaPrimeGas_convergenceDomain` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L135 [soft] `simp-law-injection` in `simp-declaration zetaPrimeGas_partitionFunction` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L137 [soft] `skeletal-proof` in `lemma zetaPrimeGas_partitionFunction` — proof appears to close via minimal tactic one-liner
  - L140 [soft] `simp-law-injection` in `simp-declaration zetaPrimeGas_eulerProduct` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L142 [soft] `skeletal-proof` in `lemma zetaPrimeGas_eulerProduct` — proof appears to close via minimal tactic one-liner
  - L197 [soft] `skeletal-proof` in `theorem weyl_denominator_limit_eq_zeta` — proof appears to close via minimal tactic one-liner
  - L207 [soft] `skeletal-proof` in `theorem weyl_denominator_limit_eq_inv_zeta` — proof appears to close via minimal tactic one-liner

