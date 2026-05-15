# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:37.678642+00:00`
Root: `lean/InfoGeometry/Canonical/OperatorThermodynamics.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **36**
- Hard: **0**
- Soft: **35**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/OperatorThermodynamics.lean` | `advisory` | 71 | 0 | 35 | 1 | 36 |

## Findings by file

### `lean/InfoGeometry/Canonical/OperatorThermodynamics.lean`
- module: `InfoGeometry.Canonical.OperatorThermodynamics`
- status: `advisory`
- debt_score: `71`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L46 [soft] `law-field-locker` in `structure-field OperatorFirstThermodynamicsPacket.modular` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L54 [soft] `law-field-locker` in `structure-field OperatorFirstThermodynamicsPacket.partitionFunction_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L57 [soft] `law-field-locker` in `structure-field OperatorFirstThermodynamicsPacket.relativeEntropyReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L60 [soft] `law-field-locker` in `structure-field OperatorFirstThermodynamicsPacket.supervolumeReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L63 [soft] `law-field-locker` in `structure-field OperatorFirstThermodynamicsPacket.relativeEntropy_eq_readout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [soft] `law-field-locker` in `structure-field OperatorFirstThermodynamicsPacket.supervolume_eq_readout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L101 [soft] `simp-law-injection` in `simp-declaration modularHamiltonian_eq_negativeLogModularOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L107 [soft] `simp-law-injection` in `simp-declaration massieuPotential_eq_log_partition` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L109 [soft] `skeletal-proof` in `theorem massieuPotential_eq_log_partition` — proof appears to close via minimal tactic one-liner
  - L113 [soft] `simp-law-injection` in `simp-declaration freeEnergy_eq_neg_log_partition` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L115 [soft] `skeletal-proof` in `theorem freeEnergy_eq_neg_log_partition` — proof appears to close via minimal tactic one-liner
  - L119 [soft] `simp-law-injection` in `simp-declaration relativeEntropy_eq_neg_massieu` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L125 [soft] `simp-law-injection` in `simp-declaration supervolumePotential_eq_freeEnergy` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L146 [soft] `law-field-locker` in `structure-field OperatorThermodynamicsPacket.modular` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L151 [soft] `law-field-locker` in `structure-field OperatorThermodynamicsPacket.partitionFunction_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L166 [soft] `law-field-locker` in `structure-field OperatorThermodynamicsPacket.massieuPotential_eq_log_partition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L169 [soft] `law-field-locker` in `structure-field OperatorThermodynamicsPacket.freeEnergy_eq_neg_log_partition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L172 [soft] `law-field-locker` in `structure-field OperatorThermodynamicsPacket.relativeEntropy_eq_neg_massieu` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L175 [soft] `law-field-locker` in `structure-field OperatorThermodynamicsPacket.supervolumePotential_eq_freeEnergy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L190 [soft] `simp-law-injection` in `simp-declaration modularHamiltonian_eq_negativeLogModularOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L196 [soft] `simp-law-injection` in `simp-declaration massieuPotential_eq_log_partition'` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L202 [soft] `simp-law-injection` in `simp-declaration freeEnergy_eq_neg_log_partition'` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L208 [soft] `simp-law-injection` in `simp-declaration relativeEntropy_eq_neg_massieu'` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L214 [soft] `simp-law-injection` in `simp-declaration supervolumePotential_eq_freeEnergy'` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L224 [soft] `simp-law-injection` in `simp-declaration partitionPotential_eq_freeEnergy` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L226 [soft] `skeletal-proof` in `theorem partitionPotential_eq_freeEnergy` — proof appears to close via minimal tactic one-liner
  - L234 [soft] `simp-law-injection` in `simp-declaration supervolumePotential_eq_partitionPotential` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L265 [soft] `simp-law-injection` in `simp-declaration toShadowPacket_partitionFunction` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L267 [soft] `skeletal-proof` in `theorem toShadowPacket_partitionFunction` — proof appears to close via minimal tactic one-liner
  - L271 [soft] `simp-law-injection` in `simp-declaration toShadowPacket_freeEnergy` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L273 [soft] `skeletal-proof` in `theorem toShadowPacket_freeEnergy` — proof appears to close via minimal tactic one-liner
  - L277 [soft] `simp-law-injection` in `simp-declaration toShadowPacket_relativeEntropy` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L279 [soft] `skeletal-proof` in `theorem toShadowPacket_relativeEntropy` — proof appears to close via minimal tactic one-liner
  - L311 [soft] `simp-law-injection` in `simp-declaration freeEnergy_eq_partitionPotential` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L317 [soft] `simp-law-injection` in `simp-declaration modularHamiltonian_eq_negativeLogModularOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

