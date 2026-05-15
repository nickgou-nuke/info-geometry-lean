# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:14.190793+00:00`
Root: `lean/InfoGeometry/Canonical/YangMillsContinuum.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **23**
- Hard: **0**
- Soft: **20**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/YangMillsContinuum.lean` | `advisory` | 43 | 0 | 20 | 3 | 23 |

## Findings by file

### `lean/InfoGeometry/Canonical/YangMillsContinuum.lean`
- module: `InfoGeometry.Canonical.YangMillsContinuum`
- status: `advisory`
- debt_score: `43`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L48 [soft] `law-field-locker` in `structure-field ModularRadonNikodymData.rnDerivative_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L75 [soft] `simp-law-injection` in `simp-declaration modularOperator_eq_rn` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L79 [soft] `simp-law-injection` in `simp-declaration modularHamiltonian_eq_neg_log_rn` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L83 [soft] `simp-law-injection` in `simp-declaration modularOperator_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L89 [soft] `simp-law-injection` in `simp-declaration modularHamiltonian_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L103 [soft] `simp-law-injection` in `simp-declaration modularAutomorphismGroup_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L111 [soft] `skeletal-proof` in `theorem hasDerivAt_modularShift_zero_eq_commutator` — proof appears to close via minimal tactic one-liner
  - L121 [advisory] `local-hypothesis-injection` in `theorem hasDerivAt_modularShift_zero_eq_commutator` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L123 [advisory] `local-hypothesis-injection` in `theorem hasDerivAt_modularShift_zero_eq_commutator` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L141 [soft] `skeletal-proof` in `lemma modularAutomorphismGroup_add` — proof appears to close via minimal tactic one-liner
  - L166 [soft] `skeletal-proof` in `theorem hasDerivAt_modularAutomorphismGroup_zero_eq_commutator` — proof appears to close via minimal tactic one-liner
  - L185 [soft] `skeletal-proof` in `theorem modularAutomorphismGroup_eq_of_time_eq` — proof appears to close via minimal tactic one-liner
  - L223 [soft] `simp-law-injection` in `simp-declaration toAdditiveModularFlow_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L236 [soft] `law-field-locker` in `structure-field TypeIIIModularInterface.modularOperator_eq_rn` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L238 [soft] `law-field-locker` in `structure-field TypeIIIModularInterface.modularHamiltonian_eq_neg_log_rn` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L240 [soft] `law-field-locker` in `structure-field TypeIIIModularInterface.modularAutomorphismGroup_additive` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L244 [soft] `law-field-locker` in `structure-field TypeIIIModularInterface.infinitesimal_generator_at_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L272 [soft] `law-field-locker` in `structure-field IBSampledFlow.pTrajectory` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L273 [soft] `law-field-locker` in `structure-field IBSampledFlow.step` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L275 [soft] `law-field-locker` in `structure-field IBSampledFlow.sampleTime` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L300 [soft] `skeletal-proof` in `theorem sinkhornControl_of_sampledIB_components` — proof appears to close via minimal tactic one-liner
  - L367 [soft] `skeletal-proof` in `theorem sinkhornControl_of_sampledIB` — proof appears to close via minimal tactic one-liner

