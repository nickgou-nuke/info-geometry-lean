# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:30.618093+00:00`
Root: `lean/InfoGeometry/Canonical/ModularSurprisalThermoPacket.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **17**
- Hard: **0**
- Soft: **6**
- Advisory: **11**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ModularSurprisalThermoPacket.lean` | `advisory` | 23 | 0 | 6 | 11 | 17 |

## Findings by file

### `lean/InfoGeometry/Canonical/ModularSurprisalThermoPacket.lean`
- module: `InfoGeometry.Canonical.ModularSurprisalThermoPacket`
- status: `advisory`
- debt_score: `23`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L49 [advisory] `existential-packaging` in `theorem representativeModularPotential_eq_negative_relativeLogDensity` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L76 [advisory] `existential-packaging` in `theorem kmsLogPartition_eq_routerMassieu` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L76 [soft] `skeletal-proof` in `theorem kmsLogPartition_eq_routerMassieu` — proof appears to close via minimal tactic one-liner
  - L85 [advisory] `existential-packaging` in `theorem finiteKMS_beta_mul_freeEnergy_eq_neg_massieu` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L95 [advisory] `existential-packaging` in `theorem finiteKMS_beta_mul_freeEnergy_eq_neg_logPartition` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L115 [advisory] `bridge-shaped-declaration` in `theorem legendre_fisher_entropy_inverse_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L142 [soft] `law-field-locker` in `structure-field ModularHamiltonianSurprisalContext.modularOperator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L143 [soft] `law-field-locker` in `structure-field ModularHamiltonianSurprisalContext.negativeLogModularOperator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L144 [soft] `law-field-locker` in `structure-field ModularHamiltonianSurprisalContext.modularHamiltonian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L145 [soft] `law-field-locker` in `structure-field ModularHamiltonianSurprisalContext.modularHamiltonian_eq_negativeLog` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L149 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L149 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L166 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L200 [advisory] `bridge-shaped-declaration` in `theorem superHamiltonian_operatorial_drazin_split_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L214 [advisory] `bridge-shaped-declaration` in `theorem superHamiltonianK_operatorial_drazin_split_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L236 [advisory] `bridge-shaped-declaration` in `theorem defectiveLogPotential_chain_rule_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

