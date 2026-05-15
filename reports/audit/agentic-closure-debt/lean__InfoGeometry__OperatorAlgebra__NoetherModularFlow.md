# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:19.032553+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/NoetherModularFlow.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **23**
- Hard: **0**
- Soft: **17**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/NoetherModularFlow.lean` | `advisory` | 40 | 0 | 17 | 6 | 23 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/NoetherModularFlow.lean`
- module: `InfoGeometry.OperatorAlgebra.NoetherModularFlow`
- status: `advisory`
- debt_score: `40`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L30 [soft] `law-field-locker` in `structure-field OperatorKillingField.derivation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L35 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L38 [soft] `skeletal-proof` in `theorem derivation_apply` — proof appears to close via minimal tactic one-liner
  - L67 [soft] `law-field-locker` in `structure-field ModularFlowCarrier.flow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L72 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L75 [soft] `skeletal-proof` in `theorem flow_apply` — proof appears to close via minimal tactic one-liner
  - L101 [soft] `law-field-locker` in `structure-field FierzRecombinationChannel.recombinationCoefficients` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L102 [soft] `law-field-locker` in `structure-field FierzRecombinationChannel.recombinationBasis` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L107 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L110 [soft] `skeletal-proof` in `theorem bilinearA_apply` — proof appears to close via minimal tactic one-liner
  - L114 [soft] `skeletal-proof` in `theorem bilinearB_apply` — proof appears to close via minimal tactic one-liner
  - L118 [soft] `skeletal-proof` in `theorem coefficient_apply` — proof appears to close via minimal tactic one-liner
  - L122 [soft] `skeletal-proof` in `theorem basis_apply` — proof appears to close via minimal tactic one-liner
  - L156 [soft] `law-field-locker` in `structure-field OperatorNoetherCharge.readoutMap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L161 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L164 [soft] `skeletal-proof` in `theorem chargeObservable_apply` — proof appears to close via minimal tactic one-liner
  - L168 [soft] `skeletal-proof` in `theorem readout_apply` — proof appears to close via minimal tactic one-liner
  - L223 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L226 [soft] `skeletal-proof` in `theorem net_apply` — proof appears to close via minimal tactic one-liner
  - L230 [soft] `skeletal-proof` in `theorem modularFlow_apply` — proof appears to close via minimal tactic one-liner
  - L234 [soft] `skeletal-proof` in `theorem killingField_apply` — proof appears to close via minimal tactic one-liner
  - L238 [soft] `skeletal-proof` in `theorem charge_apply` — proof appears to close via minimal tactic one-liner

