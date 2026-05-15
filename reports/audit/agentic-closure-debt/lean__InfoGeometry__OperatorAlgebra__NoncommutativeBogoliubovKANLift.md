# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:19.184675+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/NoncommutativeBogoliubovKANLift.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **23**
- Hard: **0**
- Soft: **12**
- Advisory: **11**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/NoncommutativeBogoliubovKANLift.lean` | `advisory` | 35 | 0 | 12 | 11 | 23 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/NoncommutativeBogoliubovKANLift.lean`
- module: `InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift`
- status: `advisory`
- debt_score: `35`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [advisory] `existential-packaging` in `structure NoncommutativeModularOperatorLift` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L46 [soft] `law-field-locker` in `structure-field NoncommutativeModularOperatorLift.noncommutativeWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L66 [soft] `law-field-locker` in `structure-field NoncommutativeModularOperatorLift.relativeHamiltonian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L69 [soft] `law-field-locker` in `structure-field NoncommutativeModularOperatorLift.modularPhase` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L89 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L101 [soft] `skeletal-proof` in `theorem connesCocycle_same_weight` — proof appears to close via minimal tactic one-liner
  - L136 [advisory] `existential-packaging` in `theorem exists_noncommuting_pair` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L142 [soft] `skeletal-proof` in `theorem typeIII_baseIntegral_eq_modularWeight_integral` — proof appears to close via minimal tactic one-liner
  - L152 [soft] `skeletal-proof` in `theorem typeIII_coreTraceOfBase_eq_coreTrace_traceOfEmbedded` — proof appears to close via minimal tactic one-liner
  - L162 [soft] `skeletal-proof` in `theorem modularWeight_integral_eq_weight_integral` — proof appears to close via minimal tactic one-liner
  - L219 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L219 [soft] `section-law-variable` in `variable P` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L273 [soft] `skeletal-proof` in `theorem phaseAxisForce_from_cartanScaleShadow` — proof appears to close via minimal tactic one-liner
  - L289 [advisory] `bridge-shaped-declaration` in `theorem diagonal_shadow_witness` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L289 [soft] `skeletal-proof` in `theorem diagonal_shadow_witness` — proof appears to close via minimal tactic one-liner
  - L336 [soft] `simp-law-injection` in `simp-declaration primary_modular_owner_is_noncommutative` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L345 [soft] `skeletal-proof` in `theorem diagonal_shadow_available` — proof appears to close via minimal tactic one-liner
  - L354 [advisory] `existential-packaging` in `theorem operator_owner_has_noncommuting_pair` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L361 [advisory] `bridge-shaped-declaration` in `theorem bridge_typeIII_baseIntegral_eq_modularWeight_integral` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L361 [advisory] `placeholder-naming` in `theorem bridge_typeIII_baseIntegral_eq_modularWeight_integral` — declaration name indicates temporary/external hypothesis surface
  - L368 [advisory] `bridge-shaped-declaration` in `theorem bridge_typeIII_coreTraceOfBase_eq_coreTrace_traceOfEmbedded` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L368 [advisory] `placeholder-naming` in `theorem bridge_typeIII_coreTraceOfBase_eq_coreTrace_traceOfEmbedded` — declaration name indicates temporary/external hypothesis surface

