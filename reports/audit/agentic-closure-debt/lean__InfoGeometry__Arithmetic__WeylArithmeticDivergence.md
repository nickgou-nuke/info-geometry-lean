# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:34.550584+00:00`
Root: `lean/InfoGeometry/Arithmetic/WeylArithmeticDivergence.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **17**
- Hard: **0**
- Soft: **10**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Arithmetic/WeylArithmeticDivergence.lean` | `advisory` | 27 | 0 | 10 | 7 | 17 |

## Findings by file

### `lean/InfoGeometry/Arithmetic/WeylArithmeticDivergence.lean`
- module: `InfoGeometry.Arithmetic.WeylArithmeticDivergence`
- status: `advisory`
- debt_score: `27`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L31 [soft] `law-field-locker` in `structure-field ArithmeticDivergenceReadout.readout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L35 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L43 [soft] `simp-law-injection` in `simp-declaration transportTemperature_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L45 [soft] `skeletal-proof` in `theorem transportTemperature_apply` — proof appears to close via minimal tactic one-liner
  - L62 [soft] `law-field-locker` in `structure-field GaugeInvariantDivergence.invariant_under_scale` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L72 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L92 [soft] `law-field-locker` in `structure-field GaugeCovariantTemperatureDivergence.weylFactor` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L94 [soft] `law-field-locker` in `structure-field GaugeCovariantTemperatureDivergence.transported_eq_factor_mul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L104 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L123 [soft] `law-field-locker` in `structure-field InversionInvariantDivergence.inversion_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L132 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L230 [soft] `law-field-locker` in `structure-field WeylGaugeDecompositionWitness.stateOfFinset` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L232 [soft] `law-field-locker` in `structure-field WeylGaugeDecompositionWitness.totalDivergence` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L235 [soft] `law-field-locker` in `structure-field WeylGaugeDecompositionWitness.weyl_decomposition_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L248 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L261 [advisory] `local-hypothesis-injection` in `theorem totalDivergence_eq_shape_of_equal_mass` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

