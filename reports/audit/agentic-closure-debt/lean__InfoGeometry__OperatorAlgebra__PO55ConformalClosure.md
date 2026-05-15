# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:20.302759+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/PO55ConformalClosure.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **29**
- Hard: **0**
- Soft: **16**
- Advisory: **13**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/PO55ConformalClosure.lean` | `advisory` | 45 | 0 | 16 | 13 | 29 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/PO55ConformalClosure.lean`
- module: `InfoGeometry.OperatorAlgebra.PO55ConformalClosure`
- status: `advisory`
- debt_score: `45`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L129 [soft] `law-field-locker` in `structure-field PO55ComponentLedger.component_convention_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L138 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L175 [soft] `law-field-locker` in `structure-field AmbientNullPair.pairing` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L191 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L221 [soft] `law-field-locker` in `structure-field NullSwapInversion.realizes_affine_inversion_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L235 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L260 [soft] `law-field-locker` in `structure-field MobiusInversionDatum.inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L262 [soft] `law-field-locker` in `structure-field MobiusInversionDatum.inv_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L269 [soft] `law-field-locker` in `structure-field MobiusInversionDatum.preserves_null` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L292 [advisory] `existential-packaging` in `def IsProjectiveFixed` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L361 [advisory] `local-hypothesis-injection` in `theorem inv_isProjectiveFixed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L365 [soft] `skeletal-proof` in `theorem scale_sq_eq_one_of_projectiveFixed_scale` — proof appears to close via minimal tactic one-liner
  - L377 [advisory] `local-hypothesis-injection` in `theorem scale_sq_eq_one_of_projectiveFixed_scale` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L385 [advisory] `local-hypothesis-injection` in `theorem scale_sq_eq_one_of_projectiveFixed_scale` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L408 [advisory] `local-hypothesis-injection` in `theorem scale_eq_one_or_neg_one_of_projectiveFixed_scale` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L411 [advisory] `local-hypothesis-injection` in `theorem scale_eq_one_or_neg_one_of_projectiveFixed_scale` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L469 [soft] `skeletal-proof` in `theorem symmetrizedReadout_inv` — proof appears to close via minimal tactic one-liner
  - L505 [advisory] `existential-packaging` in `structure PO55ConformalClosure` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L530 [soft] `law-field-locker` in `structure-field PO55ConformalClosure.affine_points_are_conformal_states` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L534 [soft] `law-field-locker` in `structure-field PO55ConformalClosure.base_action_lifts_to_PO55` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L544 [soft] `law-field-locker` in `structure-field PO55ConformalClosure.inversionPO55_rep` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L551 [soft] `law-field-locker` in `structure-field PO55ConformalClosure.inversion_affine_chart_formula_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L590 [advisory] `existential-packaging` in `theorem base_action_lifts` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L626 [soft] `law-field-locker` in `structure-field TKKPO55ClosedSymmetry.tkk_integrates_to_projective_conformal_action_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L633 [soft] `law-field-locker` in `structure-field TKKPO55ClosedSymmetry.pin55_reflection_lift_matches_PO55_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L640 [soft] `law-field-locker` in `structure-field TKKPO55ClosedSymmetry.inversion_swaps_tkk_outer_grades_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L647 [soft] `law-field-locker` in `structure-field TKKPO55ClosedSymmetry.projective_null_rays_are_closed_states_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L664 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

