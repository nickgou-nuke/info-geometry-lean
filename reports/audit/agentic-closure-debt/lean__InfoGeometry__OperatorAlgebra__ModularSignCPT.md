# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:18.490582+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ModularSignCPT.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **63**
- Hard: **0**
- Soft: **49**
- Advisory: **14**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ModularSignCPT.lean` | `advisory` | 112 | 0 | 49 | 14 | 63 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ModularSignCPT.lean`
- module: `InfoGeometry.OperatorAlgebra.ModularSignCPT`
- status: `advisory`
- debt_score: `112`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L51 [soft] `law-field-locker` in `structure-field ModularSignCPTRelations.eps_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [soft] `law-field-locker` in `structure-field ModularSignCPTRelations.J_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L59 [soft] `law-field-locker` in `structure-field ModularSignCPTRelations.J_eps_anticomm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L74 [soft] `skeletal-proof` in `theorem Kmod_eq` — proof appears to close via minimal tactic one-liner
  - L85 [soft] `skeletal-proof` in `theorem Kmod_square` — proof appears to close via minimal tactic one-liner
  - L130 [soft] `law-field-locker` in `structure-field ModularSignCPTDatum.eps_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L134 [soft] `law-field-locker` in `structure-field ModularSignCPTDatum.J_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L138 [soft] `law-field-locker` in `structure-field ModularSignCPTDatum.J_eps_anticomm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L142 [soft] `law-field-locker` in `structure-field ModularSignCPTDatum.Kmod_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L146 [soft] `law-field-locker` in `structure-field ModularSignCPTDatum.Kmod_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L155 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L175 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L200 [soft] `skeletal-proof` in `theorem Kmod_square_apply` — proof appears to close via minimal tactic one-liner
  - L213 [soft] `skeletal-proof` in `theorem complexStructure_square` — proof appears to close via minimal tactic one-liner
  - L245 [soft] `law-field-locker` in `structure-field CliffordCPTBasis.scalarUnit` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L246 [soft] `law-field-locker` in `structure-field CliffordCPTBasis.modularParity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L247 [soft] `law-field-locker` in `structure-field CliffordCPTBasis.modularReflection` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L248 [soft] `law-field-locker` in `structure-field CliffordCPTBasis.hestenesPhase` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L278 [soft] `law-field-locker` in `structure-field PartialModularSignCPTRelations.support_idempotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L282 [soft] `law-field-locker` in `structure-field PartialModularSignCPTRelations.eps_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L286 [soft] `law-field-locker` in `structure-field PartialModularSignCPTRelations.support_eps` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L290 [soft] `law-field-locker` in `structure-field PartialModularSignCPTRelations.eps_support` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L294 [soft] `law-field-locker` in `structure-field PartialModularSignCPTRelations.J_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L298 [soft] `law-field-locker` in `structure-field PartialModularSignCPTRelations.J_eps_anticomm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L302 [soft] `law-field-locker` in `structure-field PartialModularSignCPTRelations.J_support_comm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L311 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L323 [soft] `skeletal-proof` in `theorem Kmod_eq` — proof appears to close via minimal tactic one-liner
  - L328 [soft] `skeletal-proof` in `theorem Kmod_square` — proof appears to close via minimal tactic one-liner
  - L351 [soft] `skeletal-proof` in `theorem support_Kmod` — proof appears to close via minimal tactic one-liner
  - L366 [soft] `skeletal-proof` in `theorem Kmod_support` — proof appears to close via minimal tactic one-liner
  - L402 [soft] `law-field-locker` in `structure-field PartialModularSignCPTDatum.support_idempotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L406 [soft] `law-field-locker` in `structure-field PartialModularSignCPTDatum.eps_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L410 [soft] `law-field-locker` in `structure-field PartialModularSignCPTDatum.support_eps` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L414 [soft] `law-field-locker` in `structure-field PartialModularSignCPTDatum.eps_support` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L418 [soft] `law-field-locker` in `structure-field PartialModularSignCPTDatum.J_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L422 [soft] `law-field-locker` in `structure-field PartialModularSignCPTDatum.J_eps_anticomm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L426 [soft] `law-field-locker` in `structure-field PartialModularSignCPTDatum.eps_J_anticomm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L430 [soft] `law-field-locker` in `structure-field PartialModularSignCPTDatum.J_support_comm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L439 [soft] `law-field-locker` in `structure-field PartialModularSignCPTDatum.Kmod_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L443 [soft] `law-field-locker` in `structure-field PartialModularSignCPTDatum.Kmod_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L447 [soft] `law-field-locker` in `structure-field PartialModularSignCPTDatum.support_Kmod` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L451 [soft] `law-field-locker` in `structure-field PartialModularSignCPTDatum.Kmod_support` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L460 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L488 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L504 [soft] `skeletal-proof` in `theorem Kmod_square_apply` — proof appears to close via minimal tactic one-liner
  - L516 [soft] `skeletal-proof` in `theorem partialComplexStructure_square` — proof appears to close via minimal tactic one-liner
  - L563 [soft] `law-field-locker` in `structure-field DynamicModularCPTAlgebra.modularFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L566 [soft] `law-field-locker` in `structure-field DynamicModularCPTAlgebra.flow_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L569 [soft] `law-field-locker` in `structure-field DynamicModularCPTAlgebra.flow_add` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L573 [soft] `law-field-locker` in `structure-field DynamicModularCPTAlgebra.flow_mul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L587 [soft] `law-field-locker` in `structure-field DynamicModularCPTAlgebra.eps_is_sign_of_modular_hamiltonian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L593 [soft] `law-field-locker` in `structure-field DynamicModularCPTAlgebra.J_reverses_modular_flow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L596 [soft] `law-field-locker` in `structure-field DynamicModularCPTAlgebra.split_clifford_cpt_superalgebra` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L607 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L609 [soft] `simp-law-injection` in `simp-declaration modularFlow_zero_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L638 [advisory] `existential-packaging` in `def ModularSignCPTCompatibility` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L652 [advisory] `existential-packaging` in `def ModularSignCPTDatumOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L670 [advisory] `existential-packaging` in `def PartialModularSignCPTCompatibility` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L675 [advisory] `existential-packaging` in `def PartialModularSignCPTDatumOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L688 [advisory] `existential-packaging` in `def ModularSignCPTOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L705 [advisory] `existential-packaging` in `def PartialModularSignCPTOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

