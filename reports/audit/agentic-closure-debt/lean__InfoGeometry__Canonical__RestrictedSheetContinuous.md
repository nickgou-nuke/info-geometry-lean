# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:52.958485+00:00`
Root: `lean/InfoGeometry/Canonical/RestrictedSheetContinuous.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **44**
- Hard: **0**
- Soft: **36**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RestrictedSheetContinuous.lean` | `advisory` | 80 | 0 | 36 | 8 | 44 |

## Findings by file

### `lean/InfoGeometry/Canonical/RestrictedSheetContinuous.lean`
- module: `InfoGeometry.Canonical.RestrictedSheetContinuous`
- status: `advisory`
- debt_score: `80`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L23 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L25 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L39 [soft] `law-field-locker` in `structure-field RestrictedSheetContinuousEquiv.minus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L42 [soft] `law-field-locker` in `structure-field RestrictedSheetContinuousEquiv.one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L44 [soft] `law-field-locker` in `structure-field RestrictedSheetContinuousEquiv.minus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [soft] `law-field-locker` in `structure-field RestrictedSheetContinuousEquiv.minus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [soft] `law-field-locker` in `structure-field RestrictedSheetContinuousEquiv.mul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L53 [soft] `law-field-locker` in `structure-field RestrictedSheetContinuousEquiv.one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L54 [soft] `law-field-locker` in `structure-field RestrictedSheetContinuousEquiv.inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L74 [soft] `simp-law-injection` in `simp-declaration plus_mul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L77 [soft] `simp-law-injection` in `simp-declaration minus_mul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L80 [soft] `simp-law-injection` in `simp-declaration plus_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L83 [soft] `simp-law-injection` in `simp-declaration minus_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L86 [soft] `simp-law-injection` in `simp-declaration plus_inv` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L89 [soft] `simp-law-injection` in `simp-declaration minus_inv` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L97 [soft] `simp-law-injection` in `simp-declaration liftedOperator_apply_to_doubled` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L104 [soft] `simp-law-injection` in `simp-declaration plusBlockMap_liftedOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L109 [soft] `simp-law-injection` in `simp-declaration minusBlockMap_liftedOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L114 [soft] `simp-law-injection` in `simp-declaration plusToMinusBlockMap_liftedOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L119 [soft] `simp-law-injection` in `simp-declaration minusToPlusBlockMap_liftedOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L140 [soft] `simp-law-injection` in `simp-declaration plusProjectorFlux_liftedOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L146 [soft] `simp-law-injection` in `simp-declaration minusProjectorFlux_liftedOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L157 [advisory] `local-hypothesis-injection` in `theorem liftedOperator_mul` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L166 [soft] `simp-law-injection` in `simp-declaration isGaugeBalanced_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L189 [advisory] `local-hypothesis-injection` in `theorem liftedOperator_eq_dualSheetLift_of_isGaugeBalanced` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L203 [soft] `law-field-locker` in `class-field SheetRestriction.Holds` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L205 [soft] `law-field-locker` in `class-field SheetRestriction.mul_mem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L208 [soft] `law-field-locker` in `class-field SheetRestriction.inv_mem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L225 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L227 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L259 [soft] `simp-law-injection` in `simp-declaration val_mul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L263 [soft] `simp-law-injection` in `simp-declaration val_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L266 [soft] `simp-law-injection` in `simp-declaration val_inv` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L274 [soft] `simp-law-injection` in `simp-declaration liftedOperator_coe` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L277 [soft] `simp-law-injection` in `simp-declaration liftedOperator_mul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L284 [soft] `simp-law-injection` in `simp-declaration plusProjectorFlux_liftedOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L288 [soft] `simp-law-injection` in `simp-declaration minusProjectorFlux_liftedOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L312 [soft] `simp-law-injection` in `simp-declaration gaugeBalancedSheetRestriction_holds_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L325 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L326 [soft] `simp-law-injection` in `simp-declaration isGaugeBalanced` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L330 [soft] `simp-law-injection` in `simp-declaration liftedOperator_eq_dualSheetLift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L337 [soft] `simp-law-injection` in `simp-declaration plusProjectorFlux_liftedOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L342 [soft] `simp-law-injection` in `simp-declaration minusProjectorFlux_liftedOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

