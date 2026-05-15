# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:11.423264+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ConnesSpatialDerivative.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **38**
- Hard: **0**
- Soft: **30**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ConnesSpatialDerivative.lean` | `advisory` | 68 | 0 | 30 | 8 | 38 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ConnesSpatialDerivative.lean`
- module: `InfoGeometry.OperatorAlgebra.ConnesSpatialDerivative`
- status: `advisory`
- debt_score: `68`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L45 [soft] `law-field-locker` in `structure-field OperatorWeight.weight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L48 [soft] `law-field-locker` in `structure-field OperatorWeight.positivity_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L53 [soft] `law-field-locker` in `structure-field OperatorWeight.normality_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L58 [soft] `law-field-locker` in `structure-field OperatorWeight.faithfulness_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L63 [soft] `law-field-locker` in `structure-field OperatorWeight.semifiniteness_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L72 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L95 [soft] `law-field-locker` in `structure-field ModularFlow.flow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L96 [soft] `law-field-locker` in `structure-field ModularFlow.flow_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L99 [soft] `law-field-locker` in `structure-field ModularFlow.flow_add` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L102 [soft] `law-field-locker` in `structure-field ModularFlow.flow_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L105 [soft] `law-field-locker` in `structure-field ModularFlow.flow_mul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L112 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L113 [soft] `simp-law-injection` in `simp-declaration flow_zero_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L119 [soft] `simp-law-injection` in `simp-declaration flow_one_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L146 [soft] `law-field-locker` in `structure-field ConnesCocycleDerivative.modularFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L148 [soft] `law-field-locker` in `structure-field ConnesCocycleDerivative.cocycle` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L151 [soft] `law-field-locker` in `structure-field ConnesCocycleDerivative.same_weight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L155 [soft] `law-field-locker` in `structure-field ConnesCocycleDerivative.chain_rule` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L160 [soft] `law-field-locker` in `structure-field ConnesCocycleDerivative.modular_cocycle_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L170 [soft] `law-field-locker` in `structure-field ConnesCocycleDerivative.support_unitarity_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L181 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L216 [soft] `law-field-locker` in `structure-field ConnesSpatialDerivative.spatialDerivative` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L218 [soft] `law-field-locker` in `structure-field ConnesSpatialDerivative.same_weight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L222 [soft] `law-field-locker` in `structure-field ConnesSpatialDerivative.chain_rule` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L228 [soft] `law-field-locker` in `structure-field ConnesSpatialDerivative.support_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L241 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L275 [soft] `law-field-locker` in `structure-field SymmetricRelativeHamiltonianCalibration.symHamiltonian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L279 [soft] `law-field-locker` in `structure-field SymmetricRelativeHamiltonianCalibration.derived_from_spatial_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L284 [soft] `law-field-locker` in `structure-field SymmetricRelativeHamiltonianCalibration.symmetry_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L302 [soft] `law-field-locker` in `structure-field BKMMetricDatum.metric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L303 [soft] `law-field-locker` in `structure-field BKMMetricDatum.symmetric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L306 [soft] `law-field-locker` in `structure-field BKMMetricDatum.nonnegative` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L309 [soft] `law-field-locker` in `structure-field BKMMetricDatum.derived_from_spatial_derivative_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L318 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L343 [soft] `law-field-locker` in `structure-field PositiveScalarWeight.mass_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L474 [advisory] `existential-packaging` in `def ScalarSpatialDerivativeOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L489 [advisory] `existential-packaging` in `def ScalarBKMOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

