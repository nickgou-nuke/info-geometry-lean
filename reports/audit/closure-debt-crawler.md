# Lean Closure Debt Crawler Report

Generated: `2026-08-17T15:41:53.564655+00:00`
Root: `lean/InfoGeometry/Canonical/SouriauModularBregmanOperator.lean`
Authority tier: `heuristic-proxy`

## Summary

- Files scanned: **1**
- Findings: **41**
- Hard: **0**
- Soft: **34**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SouriauModularBregmanOperator.lean` | `advisory` | 75 | 0 | 34 | 7 | 41 |

## Findings by file

### `lean/InfoGeometry/Canonical/SouriauModularBregmanOperator.lean`
- module: `InfoGeometry.Canonical.SouriauModularBregmanOperator`
- status: `advisory`
- debt_score: `75`
- findings:
  - L57 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L64 [soft] `simp-law-injection` in `simp-declaration pairing_zero_right` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L72 [soft] `skeletal-proof` in `theorem pairing_eq_readout_product` — proof appears to close via minimal tactic one-liner
  - L97 [soft] `simp-law-injection` in `simp-declaration operatorBregman_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L99 [soft] `skeletal-proof` in `theorem operatorBregman_self` — proof appears to close via minimal tactic one-liner
  - L113 [soft] `skeletal-proof` in `theorem operatorBregman_invariant_of_linear_symmetry` — proof appears to close via minimal tactic one-liner
  - L125 [advisory] `local-hypothesis-injection` in `theorem operatorBregman_invariant_of_linear_symmetry` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L140 [soft] `skeletal-proof` in `theorem operatorFenchelGap_eq_zero_of_contact` — proof appears to close via minimal tactic one-liner
  - L180 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L182 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L200 [soft] `simp-law-injection` in `simp-declaration modularIdentity_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L202 [soft] `skeletal-proof` in `theorem modularIdentity_apply` — proof appears to close via minimal tactic one-liner
  - L213 [soft] `skeletal-proof` in `theorem internalPhaseAxisK_eq_phaseAxisK` — proof appears to close via minimal tactic one-liner
  - L220 [soft] `skeletal-proof` in `theorem internalPhaseAxisK_sq_eq_neg_id` — proof appears to close via minimal tactic one-liner
  - L230 [soft] `simp-law-injection` in `simp-declaration modularDeviation_identity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L232 [soft] `skeletal-proof` in `theorem modularDeviation_identity` — proof appears to close via minimal tactic one-liner
  - L242 [soft] `skeletal-proof` in `theorem modularDeltaFromHamiltonian_eq_exp_neg` — proof appears to close via minimal tactic one-liner
  - L250 [soft] `simp-law-injection` in `simp-declaration modularBetaFlow_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L252 [soft] `skeletal-proof` in `theorem modularBetaFlow_zero` — proof appears to close via minimal tactic one-liner
  - L255 [soft] `simp-law-injection` in `simp-declaration modularBetaFlow_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L257 [soft] `skeletal-proof` in `theorem modularBetaFlow_one` — proof appears to close via minimal tactic one-liner
  - L298 [soft] `simp-law-injection` in `simp-declaration modularBetaDeviation_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L300 [soft] `skeletal-proof` in `theorem modularBetaDeviation_zero` — proof appears to close via minimal tactic one-liner
  - L305 [soft] `skeletal-proof` in `theorem modularBetaDeviation_one_eq_modularDeviation_delta` — proof appears to close via minimal tactic one-liner
  - L315 [soft] `simp-law-injection` in `simp-declaration operatorStateExpectation_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L317 [soft] `skeletal-proof` in `theorem operatorStateExpectation_zero` — proof appears to close via minimal tactic one-liner
  - L336 [soft] `simp-law-injection` in `simp-declaration modularDeviationReadout_identity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L338 [soft] `skeletal-proof` in `theorem modularDeviationReadout_identity` — proof appears to close via minimal tactic one-liner
  - L348 [soft] `law-field-locker` in `structure-field BoundedSouriauModularFamily.lieObservable` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L354 [soft] `law-field-locker` in `structure-field BoundedSouriauModularFamily.modularHamiltonianK_eq_lieObservable_beta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L361 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L361 [soft] `section-law-variable` in `variable F` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L369 [soft] `skeletal-proof` in `theorem modularDelta_eq_betaFlow_one` — proof appears to close via minimal tactic one-liner
  - L379 [soft] `skeletal-proof` in `theorem deltaDeviation_eq_betaOneDeviation` — proof appears to close via minimal tactic one-liner
  - L408 [advisory] `bridge-shaped-declaration` in `def socket` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L408 [soft] `single-use-evidence-bridge` in `def socket` — bridge-shaped declaration has only 1 visible identifier occurrence(s) in the scanned root; inspect whether it exists only to close one downstream theorem instead of exposing reusable owner proof lineage
  - L417 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L417 [soft] `section-law-variable` in `variable P` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L424 [soft] `simp-law-injection` in `simp-declaration divergence_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L436 [soft] `simp-law-injection` in `simp-declaration modularDeviationDivergence_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L443 [soft] `simp-law-injection` in `simp-declaration family_deltaDeviation_divergence_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

