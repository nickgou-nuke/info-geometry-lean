# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:21.096044+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/RealHestenesONNCliffordCPT.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **4**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/RealHestenesONNCliffordCPT.lean` | `advisory` | 10 | 0 | 4 | 2 | 6 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/RealHestenesONNCliffordCPT.lean`
- module: `InfoGeometry.OperatorAlgebra.RealHestenesONNCliffordCPT`
- status: `advisory`
- debt_score: `10`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L74 [soft] `law-field-locker` in `structure-field RealHestenesONNCliffordCPTPacket.chargeConjugation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L77 [soft] `law-field-locker` in `structure-field RealHestenesONNCliffordCPTPacket.parityAction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L80 [soft] `law-field-locker` in `structure-field RealHestenesONNCliffordCPTPacket.timeReversalAction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L174 [soft] `law-field-locker` in `structure-field RealHestenesO44PinCPTPacket.pin44Cover` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L237 [advisory] `bridge-shaped-declaration` in `theorem odd_reflection_socket_available` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

