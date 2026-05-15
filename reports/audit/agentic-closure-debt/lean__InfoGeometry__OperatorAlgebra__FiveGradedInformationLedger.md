# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:14.628172+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/FiveGradedInformationLedger.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **44**
- Hard: **0**
- Soft: **38**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/FiveGradedInformationLedger.lean` | `advisory` | 82 | 0 | 38 | 6 | 44 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/FiveGradedInformationLedger.lean`
- module: `InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger`
- status: `advisory`
- debt_score: `82`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L55 [soft] `law-field-locker` in `structure-field FiveGrading.decomposition_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L58 [soft] `law-field-locker` in `structure-field FiveGrading.bracket_negOne_negOne` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L62 [soft] `law-field-locker` in `structure-field FiveGrading.bracket_posOne_posOne` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L66 [soft] `law-field-locker` in `structure-field FiveGrading.bracket_negOne_posOne` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L70 [soft] `law-field-locker` in `structure-field FiveGrading.bracket_negTwo_posTwo` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L78 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L122 [soft] `law-field-locker` in `structure-field FiveGradeProjectedAccounting.neg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L125 [soft] `law-field-locker` in `structure-field FiveGradeProjectedAccounting.pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L128 [soft] `law-field-locker` in `structure-field FiveGradeProjectedAccounting.neg_mem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L131 [soft] `law-field-locker` in `structure-field FiveGradeProjectedAccounting.pos_mem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L134 [soft] `law-field-locker` in `structure-field FiveGradeProjectedAccounting.zeroPart` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L138 [soft] `law-field-locker` in `structure-field FiveGradeProjectedAccounting.hiddenNegTwo` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L141 [soft] `law-field-locker` in `structure-field FiveGradeProjectedAccounting.hiddenPosTwo` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L144 [soft] `law-field-locker` in `structure-field FiveGradeProjectedAccounting.hiddenNegTwo_mem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L147 [soft] `law-field-locker` in `structure-field FiveGradeProjectedAccounting.hiddenPosTwo_mem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L150 [soft] `law-field-locker` in `structure-field FiveGradeProjectedAccounting.obs` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L153 [soft] `law-field-locker` in `structure-field FiveGradeProjectedAccounting.expectedObs` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L156 [soft] `law-field-locker` in `structure-field FiveGradeProjectedAccounting.expected_eq_obs_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L160 [soft] `law-field-locker` in `structure-field FiveGradeProjectedAccounting.observedCross` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L167 [soft] `law-field-locker` in `structure-field FiveGradeProjectedAccounting.observedCross_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L180 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L279 [soft] `law-field-locker` in `structure-field BlackHoleInformationLedger.memoryReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L282 [soft] `law-field-locker` in `structure-field BlackHoleInformationLedger.hidden_part_stored_as_memory` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L290 [soft] `law-field-locker` in `structure-field BlackHoleInformationLedger.full_ledger_recovery_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L299 [soft] `law-field-locker` in `structure-field BlackHoleInformationLedger.horizon_memory_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L314 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L375 [soft] `law-field-locker` in `structure-field VisibleMemoryLedger.total` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L376 [soft] `law-field-locker` in `structure-field VisibleMemoryLedger.visible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L377 [soft] `law-field-locker` in `structure-field VisibleMemoryLedger.memory` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L378 [soft] `law-field-locker` in `structure-field VisibleMemoryLedger.evolution` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L380 [soft] `law-field-locker` in `structure-field VisibleMemoryLedger.total_eq_visible_plus_memory` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L384 [soft] `law-field-locker` in `structure-field VisibleMemoryLedger.total_conserved` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L392 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L446 [soft] `law-field-locker` in `structure-field CentralExtensionAbsorption.bracket` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L448 [soft] `law-field-locker` in `structure-field CentralExtensionAbsorption.neg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L449 [soft] `law-field-locker` in `structure-field CentralExtensionAbsorption.pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L450 [soft] `law-field-locker` in `structure-field CentralExtensionAbsorption.expectedZero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L451 [soft] `law-field-locker` in `structure-field CentralExtensionAbsorption.centralDefect` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L453 [soft] `law-field-locker` in `structure-field CentralExtensionAbsorption.centralToObs` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L454 [soft] `law-field-locker` in `structure-field CentralExtensionAbsorption.observedDefect` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L457 [soft] `law-field-locker` in `structure-field CentralExtensionAbsorption.observedDefect_eq_central` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L466 [soft] `law-field-locker` in `structure-field CentralExtensionAbsorption.central_charge_memory_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L479 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

