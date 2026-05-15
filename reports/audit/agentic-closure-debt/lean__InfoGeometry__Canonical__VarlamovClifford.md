# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:09.347409+00:00`
Root: `lean/InfoGeometry/Canonical/VarlamovClifford.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **29**
- Hard: **0**
- Soft: **18**
- Advisory: **11**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/VarlamovClifford.lean` | `advisory` | 47 | 0 | 18 | 11 | 29 |

## Findings by file

### `lean/InfoGeometry/Canonical/VarlamovClifford.lean`
- module: `InfoGeometry.Canonical.VarlamovClifford`
- status: `advisory`
- debt_score: `47`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L42 [soft] `law-field-locker` in `structure-field DegenerateCliffordChart.e0_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L44 [soft] `law-field-locker` in `structure-field DegenerateCliffordChart.e1_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L45 [soft] `law-field-locker` in `structure-field DegenerateCliffordChart.e2_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L46 [soft] `law-field-locker` in `structure-field DegenerateCliffordChart.e3_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [soft] `law-field-locker` in `structure-field DegenerateCliffordChart.anti_e01` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [soft] `law-field-locker` in `structure-field DegenerateCliffordChart.anti_e02` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L50 [soft] `law-field-locker` in `structure-field DegenerateCliffordChart.anti_e03` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [soft] `law-field-locker` in `structure-field DegenerateCliffordChart.anti_e12` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [soft] `law-field-locker` in `structure-field DegenerateCliffordChart.anti_e13` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L53 [soft] `law-field-locker` in `structure-field DegenerateCliffordChart.anti_e23` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L58 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L67 [soft] `skeletal-proof` in `theorem nilpotentSignal_sq_eq_zero` — proof appears to close via minimal tactic one-liner
  - L70 [advisory] `local-hypothesis-injection` in `theorem nilpotentSignal_sq_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L88 [advisory] `local-hypothesis-injection` in `theorem regularizedSignal_mul_inverseCandidate` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L96 [advisory] `local-hypothesis-injection` in `theorem inverseCandidate_mul_regularizedSignal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L116 [soft] `law-field-locker` in `structure-field VarlamovCarrier.J_commute` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L118 [soft] `law-field-locker` in `structure-field VarlamovCarrier.J_Drazin_reflexive` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L123 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L179 [soft] `law-field-locker` in `structure-field EnvelopeVarlamovCovariance.covariance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L198 [soft] `law-field-locker` in `structure-field ExteriorDerivative.d` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L199 [soft] `law-field-locker` in `structure-field ExteriorDerivative.d_add` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L200 [soft] `law-field-locker` in `structure-field ExteriorDerivative.d_mul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L205 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L214 [advisory] `local-hypothesis-injection` in `theorem d_idempotent_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L219 [soft] `skeletal-proof` in `theorem idempotent_d_off_diagonal` — proof appears to close via minimal tactic one-liner
  - L223 [advisory] `local-hypothesis-injection` in `theorem idempotent_d_off_diagonal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L225 [advisory] `local-hypothesis-injection` in `theorem idempotent_d_off_diagonal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L240 [advisory] `local-hypothesis-injection` in `theorem idempotent_d_off_diagonal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

