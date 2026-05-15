# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:19.332855+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/O44PinCPTReflectionBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **12**
- Hard: **0**
- Soft: **9**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/O44PinCPTReflectionBridge.lean` | `advisory` | 21 | 0 | 9 | 3 | 12 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/O44PinCPTReflectionBridge.lean`
- module: `InfoGeometry.OperatorAlgebra.O44PinCPTReflectionBridge`
- status: `advisory`
- debt_score: `21`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L48 [soft] `law-field-locker` in `structure-field CPTPin44ReflectionCalibration.parity_odd` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [soft] `law-field-locker` in `structure-field CPTPin44ReflectionCalibration.timeReversal_odd` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L62 [soft] `law-field-locker` in `structure-field CPTPin44ReflectionCalibration.chargeConjugation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L65 [soft] `law-field-locker` in `structure-field CPTPin44ReflectionCalibration.parityAction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [soft] `law-field-locker` in `structure-field CPTPin44ReflectionCalibration.timeReversalAction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L71 [soft] `law-field-locker` in `structure-field CPTPin44ReflectionCalibration.charge_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L74 [soft] `law-field-locker` in `structure-field CPTPin44ReflectionCalibration.parity_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L77 [soft] `law-field-locker` in `structure-field CPTPin44ReflectionCalibration.timeReversal_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L80 [soft] `law-field-locker` in `structure-field CPTPin44ReflectionCalibration.cptAction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L93 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L136 [advisory] `bridge-shaped-declaration` in `theorem odd_reflection_socket_available` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

