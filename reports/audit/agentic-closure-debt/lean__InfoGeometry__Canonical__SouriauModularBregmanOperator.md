# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:57.793491+00:00`
Root: `lean/InfoGeometry/Canonical/SouriauModularBregmanOperator.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **47**
- Hard: **0**
- Soft: **41**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SouriauModularBregmanOperator.lean` | `advisory` | 88 | 0 | 41 | 6 | 47 |

## Findings by file

### `lean/InfoGeometry/Canonical/SouriauModularBregmanOperator.lean`
- module: `InfoGeometry.Canonical.SouriauModularBregmanOperator`
- status: `advisory`
- debt_score: `88`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L46 [soft] `law-field-locker` in `structure-field OperatorPrimalDualSocket.product` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L48 [soft] `law-field-locker` in `structure-field OperatorPrimalDualSocket.readout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [soft] `law-field-locker` in `structure-field OperatorPrimalDualSocket.product_zero_right_readout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L62 [soft] `simp-law-injection` in `simp-declaration pairing_zero_right` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L69 [soft] `skeletal-proof` in `theorem pairing_eq_readout_product` — proof appears to close via minimal tactic one-liner
  - L96 [soft] `simp-law-injection` in `simp-declaration operatorBregman_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L98 [soft] `skeletal-proof` in `theorem operatorBregman_self` — proof appears to close via minimal tactic one-liner
  - L115 [soft] `skeletal-proof` in `theorem operatorFenchelGap_eq_zero_of_contact` — proof appears to close via minimal tactic one-liner
  - L131 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L133 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L151 [soft] `simp-law-injection` in `simp-declaration modularIdentity_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L153 [soft] `skeletal-proof` in `theorem modularIdentity_apply` — proof appears to close via minimal tactic one-liner
  - L164 [soft] `skeletal-proof` in `theorem internalPhaseAxisK_eq_phaseAxisK` — proof appears to close via minimal tactic one-liner
  - L171 [soft] `skeletal-proof` in `theorem internalPhaseAxisK_sq_eq_neg_id` — proof appears to close via minimal tactic one-liner
  - L181 [soft] `simp-law-injection` in `simp-declaration modularDeviation_identity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L183 [soft] `skeletal-proof` in `theorem modularDeviation_identity` — proof appears to close via minimal tactic one-liner
  - L193 [soft] `skeletal-proof` in `theorem modularDeltaFromHamiltonian_eq_exp_neg` — proof appears to close via minimal tactic one-liner
  - L201 [soft] `simp-law-injection` in `simp-declaration modularBetaFlow_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L203 [soft] `skeletal-proof` in `theorem modularBetaFlow_zero` — proof appears to close via minimal tactic one-liner
  - L206 [soft] `simp-law-injection` in `simp-declaration modularBetaFlow_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L208 [soft] `skeletal-proof` in `theorem modularBetaFlow_one` — proof appears to close via minimal tactic one-liner
  - L216 [soft] `simp-law-injection` in `simp-declaration modularBetaDeviation_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L218 [soft] `skeletal-proof` in `theorem modularBetaDeviation_zero` — proof appears to close via minimal tactic one-liner
  - L223 [soft] `skeletal-proof` in `theorem modularBetaDeviation_one_eq_modularDeviation_delta` — proof appears to close via minimal tactic one-liner
  - L233 [soft] `simp-law-injection` in `simp-declaration operatorStateExpectation_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L235 [soft] `skeletal-proof` in `theorem operatorStateExpectation_zero` — proof appears to close via minimal tactic one-liner
  - L258 [soft] `simp-law-injection` in `simp-declaration modularDeviationReadout_identity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L260 [soft] `skeletal-proof` in `theorem modularDeviationReadout_identity` — proof appears to close via minimal tactic one-liner
  - L270 [soft] `law-field-locker` in `structure-field BoundedSouriauModularFamily.lieObservable` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L276 [soft] `law-field-locker` in `structure-field BoundedSouriauModularFamily.modularHamiltonianK_eq_lieObservable_beta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L283 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L283 [soft] `section-law-variable` in `variable F` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L291 [soft] `skeletal-proof` in `theorem modularDelta_eq_betaFlow_one` — proof appears to close via minimal tactic one-liner
  - L301 [soft] `skeletal-proof` in `theorem deltaDeviation_eq_betaOneDeviation` — proof appears to close via minimal tactic one-liner
  - L320 [soft] `law-field-locker` in `structure-field SouriauOperatorialBregmanPacket.family` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L322 [soft] `law-field-locker` in `structure-field SouriauOperatorialBregmanPacket.potential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L323 [soft] `law-field-locker` in `structure-field SouriauOperatorialBregmanPacket.gradient` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L328 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L328 [soft] `section-law-variable` in `variable P` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L334 [soft] `simp-law-injection` in `simp-declaration divergence_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L336 [soft] `skeletal-proof` in `theorem divergence_self` — proof appears to close via minimal tactic one-liner
  - L344 [soft] `simp-law-injection` in `simp-declaration modularDeviationDivergence_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L346 [soft] `skeletal-proof` in `theorem modularDeviationDivergence_self` — proof appears to close via minimal tactic one-liner
  - L349 [soft] `simp-law-injection` in `simp-declaration family_deltaDeviation_divergence_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L352 [soft] `skeletal-proof` in `theorem family_deltaDeviation_divergence_self` — proof appears to close via minimal tactic one-liner

