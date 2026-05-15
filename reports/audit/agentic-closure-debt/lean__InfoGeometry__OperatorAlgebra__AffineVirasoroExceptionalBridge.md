# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:04.990122+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/AffineVirasoroExceptionalBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **6**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/AffineVirasoroExceptionalBridge.lean` | `advisory` | 14 | 0 | 6 | 2 | 8 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/AffineVirasoroExceptionalBridge.lean`
- module: `InfoGeometry.OperatorAlgebra.AffineVirasoroExceptionalBridge`
- status: `advisory`
- debt_score: `14`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L51 [soft] `law-field-locker` in `structure-field ExceptionalAffineVirasoroBridge.finiteExceptionalLedger` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L54 [soft] `law-field-locker` in `structure-field ExceptionalAffineVirasoroBridge.affineExtensionOfFinite` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L58 [soft] `law-field-locker` in `structure-field ExceptionalAffineVirasoroBridge.virasoroActsOnAffineModes` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L65 [soft] `law-field-locker` in `structure-field ExceptionalAffineVirasoroBridge.centralChargeReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [soft] `law-field-locker` in `structure-field ExceptionalAffineVirasoroBridge.hiddenGradeMemoryReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L71 [soft] `law-field-locker` in `structure-field ExceptionalAffineVirasoroBridge.central_equals_hidden_memory` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L86 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

