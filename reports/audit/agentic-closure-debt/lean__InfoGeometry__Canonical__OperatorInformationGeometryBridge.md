# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:36.134882+00:00`
Root: `lean/InfoGeometry/Canonical/OperatorInformationGeometryBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **30**
- Hard: **0**
- Soft: **24**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/OperatorInformationGeometryBridge.lean` | `advisory` | 54 | 0 | 24 | 6 | 30 |

## Findings by file

### `lean/InfoGeometry/Canonical/OperatorInformationGeometryBridge.lean`
- module: `InfoGeometry.Canonical.OperatorInformationGeometryBridge`
- status: `advisory`
- debt_score: `54`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [soft] `law-field-locker` in `structure-field OperatorInformationGeometryCarrier.modularFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L34 [soft] `law-field-locker` in `structure-field OperatorInformationGeometryCarrier.relativeEntropy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L37 [soft] `law-field-locker` in `structure-field OperatorInformationGeometryCarrier.conditionalExpectation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L40 [soft] `law-field-locker` in `structure-field OperatorInformationGeometryCarrier.ergodicProjection` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L51 [soft] `skeletal-proof` in `theorem modularFlow_apply` — proof appears to close via minimal tactic one-liner
  - L56 [soft] `skeletal-proof` in `theorem relativeEntropy_apply` — proof appears to close via minimal tactic one-liner
  - L61 [soft] `skeletal-proof` in `theorem conditionalExpectation_apply` — proof appears to close via minimal tactic one-liner
  - L66 [soft] `skeletal-proof` in `theorem ergodicProjection_apply` — proof appears to close via minimal tactic one-liner
  - L79 [soft] `law-field-locker` in `structure-field ModularBayesianUpdateCarrier.modularFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L80 [soft] `law-field-locker` in `structure-field ModularBayesianUpdateCarrier.update` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L85 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L88 [soft] `skeletal-proof` in `theorem modularFlow_apply` — proof appears to close via minimal tactic one-liner
  - L92 [soft] `skeletal-proof` in `theorem update_apply` — proof appears to close via minimal tactic one-liner
  - L105 [soft] `law-field-locker` in `structure-field RelativeModularEntropyCarrier.relativeModularOperator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L106 [soft] `law-field-locker` in `structure-field RelativeModularEntropyCarrier.modularHamiltonian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L107 [soft] `law-field-locker` in `structure-field RelativeModularEntropyCarrier.relativeEntropy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L112 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L115 [soft] `skeletal-proof` in `theorem relativeModularOperator_apply` — proof appears to close via minimal tactic one-liner
  - L119 [soft] `skeletal-proof` in `theorem modularHamiltonian_apply` — proof appears to close via minimal tactic one-liner
  - L123 [soft] `skeletal-proof` in `theorem relativeEntropy_apply` — proof appears to close via minimal tactic one-liner
  - L135 [soft] `law-field-locker` in `structure-field ModularErgodicInvariantCarrier.modularFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L136 [soft] `law-field-locker` in `structure-field ModularErgodicInvariantCarrier.ergodicProjection` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L141 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L144 [soft] `skeletal-proof` in `theorem modularFlow_apply` — proof appears to close via minimal tactic one-liner
  - L148 [soft] `skeletal-proof` in `theorem ergodicProjection_apply` — proof appears to close via minimal tactic one-liner
  - L162 [soft] `law-field-locker` in `structure-field ClassicalChartReadoutCarrier.chartReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L167 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L170 [soft] `skeletal-proof` in `theorem chartReadout_apply` — proof appears to close via minimal tactic one-liner

