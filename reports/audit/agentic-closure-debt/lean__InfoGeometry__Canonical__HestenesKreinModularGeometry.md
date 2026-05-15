# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:14.344479+00:00`
Root: `lean/InfoGeometry/Canonical/HestenesKreinModularGeometry.lean`
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
| `lean/InfoGeometry/Canonical/HestenesKreinModularGeometry.lean` | `advisory` | 71 | 0 | 35 | 1 | 36 |

## Findings by file

### `lean/InfoGeometry/Canonical/HestenesKreinModularGeometry.lean`
- module: `InfoGeometry.Canonical.HestenesKreinModularGeometry`
- status: `advisory`
- debt_score: `71`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L53 [soft] `law-field-locker` in `structure-field KreinHestenesModularDatum.fundamentalSymmetry_involution` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L72 [soft] `law-field-locker` in `structure-field KreinHestenesModularDatum.modularWeight_generator_statement` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L83 [soft] `law-field-locker` in `structure-field KreinHestenesModularDatum.generator_krein_compatible_statement` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L143 [soft] `simp-law-injection` in `simp-declaration modularDerivation_generator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L146 [soft] `skeletal-proof` in `theorem modularDerivation_generator` — proof appears to close via minimal tactic one-liner
  - L149 [soft] `simp-law-injection` in `simp-declaration modularGenerator_isModularMonogenic` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L188 [soft] `law-field-locker` in `structure-field HestenesRotorFlow.rotor` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L190 [soft] `law-field-locker` in `structure-field HestenesRotorFlow.rotorInv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L193 [soft] `law-field-locker` in `structure-field HestenesRotorFlow.rotor_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L197 [soft] `law-field-locker` in `structure-field HestenesRotorFlow.rotorInv_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L201 [soft] `law-field-locker` in `structure-field HestenesRotorFlow.rotor_left_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L205 [soft] `law-field-locker` in `structure-field HestenesRotorFlow.rotor_right_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L209 [soft] `law-field-locker` in `structure-field HestenesRotorFlow.generator_relation_statement` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L219 [soft] `law-field-locker` in `structure-field HestenesRotorFlow.fixedByFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L222 [soft] `law-field-locker` in `structure-field HestenesRotorFlow.fixedByFlow_iff_monogenic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L283 [soft] `law-field-locker` in `structure-field KreinFredholmDeterminantContract.kreinTraceClass_statement` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L292 [soft] `law-field-locker` in `structure-field KreinFredholmDeterminantContract.determinant_formula_statement` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L341 [soft] `law-field-locker` in `structure-field RelativeKreinModularFredholmDatum.modularDefect_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L346 [soft] `law-field-locker` in `structure-field RelativeKreinModularFredholmDatum.fredholm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L353 [soft] `law-field-locker` in `structure-field RelativeKreinModularFredholmDatum.relativePartitionReadout_eq_det` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L357 [soft] `law-field-locker` in `structure-field RelativeKreinModularFredholmDatum.relativeCountDensity_statement` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L414 [soft] `law-field-locker` in `structure-field KreinModularCoreProjectorWitness.core_idempotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L418 [soft] `law-field-locker` in `structure-field KreinModularCoreProjectorWitness.nil_idempotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L422 [soft] `law-field-locker` in `structure-field KreinModularCoreProjectorWitness.core_nil_disjoint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L426 [soft] `law-field-locker` in `structure-field KreinModularCoreProjectorWitness.nil_core_disjoint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L430 [soft] `law-field-locker` in `structure-field KreinModularCoreProjectorWitness.core_add_nil` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L434 [soft] `law-field-locker` in `structure-field KreinModularCoreProjectorWitness.core_commutes_with_generator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L439 [soft] `law-field-locker` in `structure-field KreinModularCoreProjectorWitness.core_krein_compatible_statement` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L449 [soft] `law-field-locker` in `structure-field KreinModularCoreProjectorWitness.spectral_boundary_statement` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L466 [soft] `simp-law-injection` in `simp-declaration core_idempotent_holds` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L472 [soft] `simp-law-injection` in `simp-declaration nil_idempotent_holds` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L478 [soft] `simp-law-injection` in `simp-declaration core_idempotent_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L487 [soft] `simp-law-injection` in `simp-declaration nil_idempotent_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L551 [soft] `law-field-locker` in `structure-field HestenesKreinModularFredholmBridge.core_fredholm_count_statement` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L572 [soft] `simp-law-injection` in `simp-declaration modularGenerator_is_monogenic` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

