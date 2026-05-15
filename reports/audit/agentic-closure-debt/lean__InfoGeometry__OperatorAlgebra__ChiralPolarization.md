# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:07.052440+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ChiralPolarization.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **41**
- Hard: **0**
- Soft: **33**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ChiralPolarization.lean` | `advisory` | 74 | 0 | 33 | 8 | 41 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ChiralPolarization.lean`
- module: `InfoGeometry.OperatorAlgebra.ChiralPolarization`
- status: `advisory`
- debt_score: `74`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L31 [soft] `law-field-locker` in `structure-field KreinMetricDatum.eta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L32 [soft] `law-field-locker` in `structure-field KreinMetricDatum.eta_self_adjoint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L33 [soft] `law-field-locker` in `structure-field KreinMetricDatum.eta_involutive` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L53 [advisory] `existential-packaging` in `def SameProjectiveRay` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L61 [advisory] `existential-packaging` in `def IsNilpotentElement` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L108 [advisory] `existential-packaging` in `def IsLeftZeroDivisor` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L118 [advisory] `existential-packaging` in `def IsRightZeroDivisor` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L164 [soft] `law-field-locker` in `class-field NoSquareZero.eq_zero_of_square_eq_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L205 [soft] `law-field-locker` in `structure-field CircularPolarization.chi_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L215 [soft] `law-field-locker` in `structure-field CircularPolarization.P_left_def` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L219 [soft] `law-field-locker` in `structure-field CircularPolarization.P_right_def` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L223 [soft] `law-field-locker` in `structure-field CircularPolarization.P_left_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L227 [soft] `law-field-locker` in `structure-field CircularPolarization.P_right_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L231 [soft] `law-field-locker` in `structure-field CircularPolarization.P_left_mul_right` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L235 [soft] `law-field-locker` in `structure-field CircularPolarization.P_right_mul_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L239 [soft] `law-field-locker` in `structure-field CircularPolarization.P_sum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L247 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L248 [soft] `simp-law-injection` in `simp-declaration left_idempotent` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L254 [soft] `simp-law-injection` in `simp-declaration right_idempotent` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L260 [soft] `simp-law-injection` in `simp-declaration left_mul_right` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L266 [soft] `simp-law-injection` in `simp-declaration right_mul_left` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L296 [soft] `law-field-locker` in `structure-field PhasePreservingAlgebraMap.toLinearMap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L297 [soft] `law-field-locker` in `structure-field PhasePreservingAlgebraMap.map_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L300 [soft] `law-field-locker` in `structure-field PhasePreservingAlgebraMap.map_mul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L304 [soft] `law-field-locker` in `structure-field PhasePreservingAlgebraMap.map_chi` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L315 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L341 [soft] `law-field-locker` in `structure-field ModuleCircularPolarization.chi` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L343 [soft] `law-field-locker` in `structure-field ModuleCircularPolarization.chi_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L347 [soft] `law-field-locker` in `structure-field ModuleCircularPolarization.P_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L349 [soft] `law-field-locker` in `structure-field ModuleCircularPolarization.P_right` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L350 [soft] `law-field-locker` in `structure-field ModuleCircularPolarization.P_left_def` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L355 [soft] `law-field-locker` in `structure-field ModuleCircularPolarization.P_right_def` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L360 [soft] `law-field-locker` in `structure-field ModuleCircularPolarization.P_left_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L363 [soft] `law-field-locker` in `structure-field ModuleCircularPolarization.P_right_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L366 [soft] `law-field-locker` in `structure-field ModuleCircularPolarization.P_left_comp_right` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L369 [soft] `law-field-locker` in `structure-field ModuleCircularPolarization.P_right_comp_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L372 [soft] `law-field-locker` in `structure-field ModuleCircularPolarization.P_sum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L389 [soft] `law-field-locker` in `structure-field PhasePreservingLinearMap.toLinearMap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L390 [soft] `law-field-locker` in `structure-field PhasePreservingLinearMap.preserves_chi` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L401 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

