# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:04.871477+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/AffineVirasoroBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **33**
- Hard: **0**
- Soft: **25**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/AffineVirasoroBridge.lean` | `advisory` | 58 | 0 | 25 | 8 | 33 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/AffineVirasoroBridge.lean`
- module: `InfoGeometry.OperatorAlgebra.AffineVirasoroBridge`
- status: `advisory`
- debt_score: `58`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L50 [soft] `law-field-locker` in `structure-field VirasoroDatum.Lmode` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [soft] `law-field-locker` in `structure-field VirasoroDatum.central_commutes` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [soft] `law-field-locker` in `structure-field VirasoroDatum.virasoro_bracket` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L83 [soft] `law-field-locker` in `structure-field VirasoroCentralCoefficientNormalization.coeff` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L84 [soft] `law-field-locker` in `structure-field VirasoroCentralCoefficientNormalization.coeff_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L89 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L128 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L187 [soft] `law-field-locker` in `structure-field SugawaraDatum.sugawara_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L193 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L248 [soft] `law-field-locker` in `structure-field AffineCurrentDatum.Current` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L252 [soft] `law-field-locker` in `structure-field AffineCurrentDatum.kCentral_commutes` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L255 [soft] `law-field-locker` in `structure-field AffineCurrentDatum.killingForm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L258 [soft] `law-field-locker` in `structure-field AffineCurrentDatum.affine_bracket` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L272 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L335 [soft] `law-field-locker` in `structure-field AffineVirasoroBridgeDatum.virasoro_acts_on_currents` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L355 [soft] `law-field-locker` in `structure-field AffineVirasoroBridgeDatum.centralCharge_eq_sugawara` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L371 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L439 [soft] `law-field-locker` in `structure-field ExceptionalAffineVirasoroCalibration.finite_dimension_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L442 [soft] `law-field-locker` in `structure-field ExceptionalAffineVirasoroCalibration.dual_coxeter_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L445 [soft] `law-field-locker` in `structure-field ExceptionalAffineVirasoroCalibration.level_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L485 [soft] `law-field-locker` in `structure-field SugawaraModeConstructionDatum.modeSum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L488 [soft] `law-field-locker` in `structure-field SugawaraModeConstructionDatum.sugawara_mode_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L506 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L544 [soft] `law-field-locker` in `structure-field ModularHelicalCalibration.modularFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L547 [soft] `law-field-locker` in `structure-field ModularHelicalCalibration.L0Flow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L550 [soft] `law-field-locker` in `structure-field ModularHelicalCalibration.modularFlow_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L553 [soft] `law-field-locker` in `structure-field ModularHelicalCalibration.modularFlow_add` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L558 [soft] `law-field-locker` in `structure-field ModularHelicalCalibration.L0Flow_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L561 [soft] `law-field-locker` in `structure-field ModularHelicalCalibration.modular_flow_is_L0` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L577 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L638 [soft] `skeletal-proof` in `theorem affine_symmetry_left_inverse` — proof appears to close via minimal tactic one-liner
  - L648 [soft] `skeletal-proof` in `theorem affine_symmetry_right_inverse` — proof appears to close via minimal tactic one-liner

