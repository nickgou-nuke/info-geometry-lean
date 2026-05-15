# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:26.646504+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/VortexPunctureRepair.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **7**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/VortexPunctureRepair.lean` | `advisory` | 20 | 0 | 7 | 6 | 13 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/VortexPunctureRepair.lean`
- module: `InfoGeometry.OperatorAlgebra.VortexPunctureRepair`
- status: `advisory`
- debt_score: `20`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [soft] `law-field-locker` in `structure-field LocalizedPuncture.singular` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L40 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L69 [soft] `law-field-locker` in `structure-field VortexCoreDatum.vortex_core_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L84 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L108 [soft] `law-field-locker` in `structure-field MajoranaPlugWitness.core_eq_plug` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L111 [soft] `law-field-locker` in `structure-field MajoranaPlugWitness.protection_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L127 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L165 [soft] `law-field-locker` in `structure-field SubgapRepairWitness.core_eq_subgap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L168 [soft] `law-field-locker` in `structure-field SubgapRepairWitness.resolved` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L180 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L216 [soft] `law-field-locker` in `structure-field VortexRepairBridge.repair_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L232 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

