# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:43.749886+00:00`
Root: `lean/InfoGeometry/Canonical/PrimeGasMaxEnt.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **21**
- Hard: **0**
- Soft: **18**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/PrimeGasMaxEnt.lean` | `advisory` | 39 | 0 | 18 | 3 | 21 |

## Findings by file

### `lean/InfoGeometry/Canonical/PrimeGasMaxEnt.lean`
- module: `InfoGeometry.Canonical.PrimeGasMaxEnt`
- status: `advisory`
- debt_score: `39`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L39 [soft] `law-field-locker` in `structure-field PrimeGasSymmetry.V4_Weyl` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L40 [soft] `law-field-locker` in `structure-field PrimeGasSymmetry.V4_tensor_V4` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L41 [soft] `law-field-locker` in `structure-field PrimeGasSymmetry.V4_tensor_V4_tensor_V4` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L42 [soft] `law-field-locker` in `structure-field PrimeGasSymmetry.kleinBottleQuotient` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `law-field-locker` in `structure-field PrimeGasSymmetry.moebiusDiscreteTwist` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L44 [soft] `law-field-locker` in `structure-field PrimeGasSymmetry.splitCl11Atom` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L61 [soft] `law-field-locker` in `structure-field PrimeGasJaynesData.idealFermionGas` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L62 [soft] `law-field-locker` in `structure-field PrimeGasJaynesData.primeOccupationLogEnergy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L63 [soft] `law-field-locker` in `structure-field PrimeGasJaynesData.eulerProductPartition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L66 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L68 [soft] `law-field-locker` in `structure-field PrimeGasJaynesData.instance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L114 [soft] `skeletal-proof` in `theorem partitionFunction_pos` — proof appears to close via minimal tactic one-liner
  - L123 [soft] `skeletal-proof` in `theorem gibbsMeasure_ac` — proof appears to close via minimal tactic one-liner
  - L131 [soft] `skeletal-proof` in `theorem rnDeriv_gibbsMeasure_eq` — proof appears to close via minimal tactic one-liner
  - L143 [soft] `skeletal-proof` in `theorem rnDeriv_gibbsMeasure_toReal_eq` — proof appears to close via minimal tactic one-liner
  - L160 [soft] `law-field-locker` in `structure-field PrimeGasPartitionPacket.lam` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L161 [soft] `law-field-locker` in `structure-field PrimeGasPartitionPacket.hInt` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L162 [soft] `law-field-locker` in `structure-field PrimeGasPartitionPacket.partitionFunction_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L164 [soft] `law-field-locker` in `structure-field PrimeGasPartitionPacket.rnDeriv_gibbsMeasure_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L178 [advisory] `existential-packaging` in `def PrimeGasJaynesConjecture` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

