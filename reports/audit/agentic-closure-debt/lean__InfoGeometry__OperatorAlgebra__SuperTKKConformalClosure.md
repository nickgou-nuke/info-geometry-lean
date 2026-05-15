# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:23.821648+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/SuperTKKConformalClosure.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **46**
- Hard: **0**
- Soft: **29**
- Advisory: **17**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/SuperTKKConformalClosure.lean` | `advisory` | 75 | 0 | 29 | 17 | 46 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/SuperTKKConformalClosure.lean`
- module: `InfoGeometry.OperatorAlgebra.SuperTKKConformalClosure`
- status: `advisory`
- debt_score: `75`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L62 [soft] `law-field-locker` in `structure-field FiveGrading.decomposition_symm_apply` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L72 [soft] `law-field-locker` in `structure-field FiveGrading.bracket_neg_one_pos_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L76 [soft] `law-field-locker` in `structure-field FiveGrading.bracket_zero_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L80 [soft] `law-field-locker` in `structure-field FiveGrading.bracket_pos_one_pos_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L84 [soft] `law-field-locker` in `structure-field FiveGrading.bracket_neg_one_neg_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L88 [soft] `law-field-locker` in `structure-field FiveGrading.bracket_zero_pos_two` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L92 [soft] `law-field-locker` in `structure-field FiveGrading.bracket_zero_neg_two` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L96 [soft] `law-field-locker` in `structure-field FiveGrading.bracket_pos_two_pos_two_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L104 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L111 [soft] `skeletal-proof` in `theorem recompose_coordinates` — proof appears to close via minimal tactic one-liner
  - L117 [soft] `skeletal-proof` in `theorem coordinates_recompose` — proof appears to close via minimal tactic one-liner
  - L201 [advisory] `existential-packaging` in `structure SuperchargeSquareRoot` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L221 [soft] `law-field-locker` in `structure-field SuperchargeSquareRoot.superAnticommutator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L225 [soft] `law-field-locker` in `structure-field SuperchargeSquareRoot.superAnticommutator_symm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L229 [soft] `law-field-locker` in `structure-field SuperchargeSquareRoot.mixed_chirality_mem_translation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L238 [soft] `law-field-locker` in `structure-field SuperchargeSquareRoot.left_left_mem_pos_two` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L248 [soft] `law-field-locker` in `structure-field SuperchargeSquareRoot.right_right_mem_neg_two` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L258 [soft] `law-field-locker` in `structure-field SuperchargeSquareRoot.mixed_translation_surjective` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L267 [soft] `law-field-locker` in `structure-field SuperchargeSquareRoot.left_left_pos_two_surjective` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L276 [soft] `law-field-locker` in `structure-field SuperchargeSquareRoot.right_right_neg_two_surjective` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L292 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L342 [advisory] `existential-packaging` in `theorem exists_mixed_supercharge_for_translation` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L352 [advisory] `existential-packaging` in `theorem exists_left_left_supercharge_for_pos_two` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L362 [advisory] `existential-packaging` in `theorem exists_right_right_supercharge_for_neg_two` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L374 [advisory] `existential-packaging` in `structure SuperTKKDefectAbsorption` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L397 [soft] `law-field-locker` in `structure-field SuperTKKDefectAbsorption.geometryLift` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L401 [soft] `law-field-locker` in `structure-field SuperTKKDefectAbsorption.defect_as_left_left_supercharge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L425 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L427 [advisory] `existential-packaging` in `theorem closure_defect_has_left_left_square` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L461 [advisory] `existential-packaging` in `theorem mixed_supercharges_generate_translation` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L471 [advisory] `existential-packaging` in `theorem left_chirality_generates_grade_two_charge` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L505 [advisory] `local-hypothesis-injection` in `theorem lifted_ricciFlux_mem_grade_two_of_curvature_stationary` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L510 [advisory] `existential-packaging` in `theorem exists_left_left_square_for_lifted_ricciFlux_of_curvature_stationary` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L547 [soft] `law-field-locker` in `structure-field BPSCentralChargeLedger.energy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L548 [soft] `law-field-locker` in `structure-field BPSCentralChargeLedger.chargeNorm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L549 [soft] `law-field-locker` in `structure-field BPSCentralChargeLedger.heat` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L550 [soft] `law-field-locker` in `structure-field BPSCentralChargeLedger.chargeNorm_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L554 [soft] `law-field-locker` in `structure-field BPSCentralChargeLedger.chargeNorm_le_energy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L558 [soft] `law-field-locker` in `structure-field BPSCentralChargeLedger.heat_eq_energy_sub_chargeNorm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L566 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L572 [soft] `skeletal-proof` in `theorem energy_nonneg` — proof appears to close via minimal tactic one-liner
  - L633 [soft] `law-field-locker` in `structure-field BPSDefectBridge.chargeNormTrace` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L635 [soft] `law-field-locker` in `structure-field BPSDefectBridge.chargeNorm_eq_trace_defect` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L653 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L683 [advisory] `existential-packaging` in `def SuperTKKDefectAbsorptionOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

