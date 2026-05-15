# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:05.469268+00:00`
Root: `lean/InfoGeometry/Canonical/DrazinSupergradedWeylSocket.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **27**
- Hard: **0**
- Soft: **20**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DrazinSupergradedWeylSocket.lean` | `advisory` | 47 | 0 | 20 | 7 | 27 |

## Findings by file

### `lean/InfoGeometry/Canonical/DrazinSupergradedWeylSocket.lean`
- module: `InfoGeometry.Canonical.DrazinSupergradedWeylSocket`
- status: `advisory`
- debt_score: `47`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L55 [soft] `law-field-locker` in `structure-field SuperGrading.involutive` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L107 [soft] `law-field-locker` in `structure-field StableScaledProjector.scaled_idempotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L125 [soft] `law-field-locker` in `structure-field StableFermionObservable.obs_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L173 [soft] `law-field-locker` in `structure-field SupergradedStratumCompatibility.role` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L174 [soft] `law-field-locker` in `structure-field SupergradedStratumCompatibility.ghost_iff_delta10` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L178 [soft] `law-field-locker` in `structure-field SupergradedStratumCompatibility.stableComposite_iff_delta11` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L182 [soft] `law-field-locker` in `structure-field SupergradedStratumCompatibility.bosonicKernel_iff_delta0` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L210 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L240 [advisory] `existential-packaging` in `theorem invertible_stratum_inverted_ae` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L300 [soft] `law-field-locker` in `structure-field DrazinCARCCRCompatibilityAssumption.primitiveFermion` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L302 [soft] `law-field-locker` in `structure-field DrazinCARCCRCompatibilityAssumption.stableFermionObservable` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L304 [soft] `law-field-locker` in `structure-field DrazinCARCCRCompatibilityAssumption.carObservable` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L306 [soft] `law-field-locker` in `structure-field DrazinCARCCRCompatibilityAssumption.ccrObservable` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L308 [soft] `law-field-locker` in `structure-field DrazinCARCCRCompatibilityAssumption.ghostObservable` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L310 [soft] `law-field-locker` in `structure-field DrazinCARCCRCompatibilityAssumption.ghost_square_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L314 [soft] `law-field-locker` in `structure-field DrazinCARCCRCompatibilityAssumption.primitive_fermion_is_odd` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L318 [soft] `law-field-locker` in `structure-field DrazinCARCCRCompatibilityAssumption.primitive_fermion_is_nilpotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L322 [soft] `law-field-locker` in `structure-field DrazinCARCCRCompatibilityAssumption.stable_fermion_is_even` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L326 [soft] `law-field-locker` in `structure-field DrazinCARCCRCompatibilityAssumption.stable_fermion_lives_on_horizon` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L330 [soft] `law-field-locker` in `structure-field DrazinCARCCRCompatibilityAssumption.car_lives_on_horizon` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L334 [soft] `law-field-locker` in `structure-field DrazinCARCCRCompatibilityAssumption.ccr_scale_readout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L336 [soft] `law-field-locker` in `structure-field DrazinCARCCRCompatibilityAssumption.ccr_scale_eq_expectation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L344 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L356 [advisory] `bridge-shaped-declaration` in `theorem primitive_fermion_odd_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L364 [advisory] `bridge-shaped-declaration` in `theorem primitive_fermion_nilpotent_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L372 [advisory] `bridge-shaped-declaration` in `theorem stable_fermion_even_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

