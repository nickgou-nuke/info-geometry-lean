# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:44.298076+00:00`
Root: `lean/InfoGeometry/Canonical/PrimeGeodesicEmergence.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **12**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/PrimeGeodesicEmergence.lean` | `advisory` | 25 | 0 | 12 | 1 | 13 |

## Findings by file

### `lean/InfoGeometry/Canonical/PrimeGeodesicEmergence.lean`
- module: `InfoGeometry.Canonical.PrimeGeodesicEmergence`
- status: `advisory`
- debt_score: `25`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [soft] `law-field-locker` in `structure-field PrimeGeodesicOrbit.primitive` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L36 [soft] `law-field-locker` in `structure-field PrimeGeodesicOrbit.irreducible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [soft] `skeletal-proof` in `theorem energy_eq_log_label` — proof appears to close via minimal tactic one-liner
  - L65 [soft] `law-field-locker` in `structure-field PrimeGeodesicEmergence.boostBivector_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L66 [soft] `law-field-locker` in `structure-field PrimeGeodesicEmergence.discreteDilationSemigroup` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [soft] `law-field-locker` in `structure-field PrimeGeodesicEmergence.fermionicPrimitiveOrbit` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L69 [soft] `law-field-locker` in `structure-field PrimeGeodesicEmergence.integerFockSpace` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L70 [soft] `law-field-locker` in `structure-field PrimeGeodesicEmergence.squareFreeSupport` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L72 [soft] `law-field-locker` in `structure-field PrimeGeodesicEmergence.V4_projection` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L73 [soft] `law-field-locker` in `structure-field PrimeGeodesicEmergence.moebiusParity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L74 [soft] `law-field-locker` in `structure-field PrimeGeodesicEmergence.eulerProductPartition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L89 [soft] `law-field-locker` in `structure-field PrimeGeodesicEmergencePacket.orbitEnergy_eq_log_label` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

