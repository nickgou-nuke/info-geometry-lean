# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:14.480082+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/FiveGradedDefectAbsorption.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **33**
- Hard: **0**
- Soft: **26**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/FiveGradedDefectAbsorption.lean` | `advisory` | 59 | 0 | 26 | 7 | 33 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/FiveGradedDefectAbsorption.lean`
- module: `InfoGeometry.OperatorAlgebra.FiveGradedDefectAbsorption`
- status: `advisory`
- debt_score: `59`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L84 [soft] `law-field-locker` in `structure-field ThreeGradeClosureDefect.defect` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L85 [soft] `law-field-locker` in `structure-field ThreeGradeClosureDefect.defect_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L98 [soft] `law-field-locker` in `structure-field DefectAbsorbedInPlusTwo.defectToPlusTwo` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L100 [soft] `law-field-locker` in `structure-field DefectAbsorbedInPlusTwo.defect_mem_plus_two` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L104 [soft] `law-field-locker` in `structure-field DefectAbsorbedInPlusTwo.absorption_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L121 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L149 [soft] `law-field-locker` in `structure-field TKKDefectAbsorbedInPlusTwo.defectToPlusTwo` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L151 [soft] `law-field-locker` in `structure-field TKKDefectAbsorbedInPlusTwo.defect_mem_plus_two` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L155 [soft] `law-field-locker` in `structure-field TKKDefectAbsorbedInPlusTwo.plusTwoReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L158 [soft] `law-field-locker` in `structure-field TKKDefectAbsorbedInPlusTwo.closureDefect_eq_plusTwoReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L172 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L219 [soft] `law-field-locker` in `structure-field BlackHoleFiveGradeLedger.visibleState` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L222 [soft] `law-field-locker` in `structure-field BlackHoleFiveGradeLedger.hiddenState` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L225 [soft] `law-field-locker` in `structure-field BlackHoleFiveGradeLedger.memory` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L228 [soft] `law-field-locker` in `structure-field BlackHoleFiveGradeLedger.memoryToPlusTwo` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L231 [soft] `law-field-locker` in `structure-field BlackHoleFiveGradeLedger.memory_mem_plus_two` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L235 [soft] `law-field-locker` in `structure-field BlackHoleFiveGradeLedger.local_reduction_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L241 [soft] `law-field-locker` in `structure-field BlackHoleFiveGradeLedger.full_ledger_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L253 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L277 [soft] `law-field-locker` in `structure-field GradeTwoInformationLedger.total` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L278 [soft] `law-field-locker` in `structure-field GradeTwoInformationLedger.visible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L279 [soft] `law-field-locker` in `structure-field GradeTwoInformationLedger.gradeTwo` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L280 [soft] `law-field-locker` in `structure-field GradeTwoInformationLedger.total_eq_visible_plus_gradeTwo` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L284 [soft] `law-field-locker` in `structure-field GradeTwoInformationLedger.evolution` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L287 [soft] `law-field-locker` in `structure-field GradeTwoInformationLedger.total_conserved` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L295 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L348 [soft] `law-field-locker` in `structure-field BPSBoundDatum.mass` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L350 [soft] `law-field-locker` in `structure-field BPSBoundDatum.centralNorm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L353 [soft] `law-field-locker` in `structure-field BPSBoundDatum.centralNorm_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L357 [soft] `law-field-locker` in `structure-field BPSBoundDatum.bps_bound` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L372 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L426 [advisory] `existential-packaging` in `def BPSBoundOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

