# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:53.100320+00:00`
Root: `lean/InfoGeometry/Canonical/RestrictedVolumeCharacter.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **49**
- Hard: **0**
- Soft: **43**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RestrictedVolumeCharacter.lean` | `advisory` | 92 | 0 | 43 | 6 | 49 |

## Findings by file

### `lean/InfoGeometry/Canonical/RestrictedVolumeCharacter.lean`
- module: `InfoGeometry.Canonical.RestrictedVolumeCharacter`
- status: `advisory`
- debt_score: `92`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L19 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L34 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L36 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L45 [soft] `simp-law-injection` in `simp-declaration dualSheetPairLift_apply_to_doubled` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L54 [soft] `simp-law-injection` in `simp-declaration dualSheetLift_eq_dualSheetPairLift_same` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L60 [soft] `simp-law-injection` in `simp-declaration plusBlockMap_dualSheetPairLift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L68 [soft] `simp-law-injection` in `simp-declaration minusBlockMap_dualSheetPairLift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L76 [soft] `simp-law-injection` in `simp-declaration plusToMinusBlockMap_dualSheetPairLift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L84 [soft] `simp-law-injection` in `simp-declaration minusToPlusBlockMap_dualSheetPairLift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L108 [soft] `simp-law-injection` in `simp-declaration plusProjectorFlux_dualSheetPairLift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L116 [soft] `simp-law-injection` in `simp-declaration minusProjectorFlux_dualSheetPairLift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L131 [soft] `simp-law-injection` in `simp-declaration dualSheetDiagonalScalarOp_apply_to_doubled` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L141 [soft] `simp-law-injection` in `simp-declaration dualSheetDiagonalScalarOp_eq_smul_proj_add` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L149 [soft] `simp-law-injection` in `simp-declaration plusBlockMap_dualSheetDiagonalScalarOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L159 [soft] `simp-law-injection` in `simp-declaration minusBlockMap_dualSheetDiagonalScalarOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L169 [soft] `simp-law-injection` in `simp-declaration plusToMinusBlockMap_dualSheetDiagonalScalarOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L178 [soft] `simp-law-injection` in `simp-declaration minusToPlusBlockMap_dualSheetDiagonalScalarOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L187 [soft] `simp-law-injection` in `simp-declaration plusProjectorFlux_dualSheetDiagonalScalarOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L196 [soft] `simp-law-injection` in `simp-declaration minusProjectorFlux_dualSheetDiagonalScalarOp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L205 [soft] `simp-law-injection` in `simp-declaration dualSheetDiagonalScalarOp_same` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L212 [soft] `simp-law-injection` in `simp-declaration dualSheetDiagonalScalarOp_one_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L218 [soft] `simp-law-injection` in `simp-declaration dualSheetDiagonalScalarOp_one_neg_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L224 [soft] `simp-law-injection` in `simp-declaration dualSheetDiagonalScalarOp_one_neg_one_eq_spectral_epsilon` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L252 [soft] `simp-law-injection` in `simp-declaration chiralDilationPart_eq_core` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L257 [soft] `simp-law-injection` in `simp-declaration commonWeylScale_add_relativeSheetScale` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L263 [soft] `simp-law-injection` in `simp-declaration commonWeylScale_sub_relativeSheetScale` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L271 [soft] `skeletal-proof` in `theorem dualSheetDiagonalScalarOp_eq_isotropicWeylPart_add_chiralDilationPart` — proof appears to close via minimal tactic one-liner
  - L283 [advisory] `local-hypothesis-injection` in `theorem dualSheetDiagonalScalarOp_eq_isotropicWeylPart_add_chiralDilationPart` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L290 [advisory] `local-hypothesis-injection` in `theorem dualSheetDiagonalScalarOp_eq_isotropicWeylPart_add_chiralDilationPart` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L292 [soft] `simp-law-injection` in `simp-declaration commonWeylScale_exp_pair` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L299 [soft] `simp-law-injection` in `simp-declaration relativeSheetScale_exp_pair` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L357 [soft] `law-field-locker` in `structure-field RestrictedSheetEquiv.minus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L360 [soft] `law-field-locker` in `structure-field RestrictedSheetEquiv.one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L362 [soft] `law-field-locker` in `structure-field RestrictedSheetEquiv.minus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L367 [soft] `law-field-locker` in `structure-field RestrictedSheetEquiv.minus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L370 [soft] `law-field-locker` in `structure-field RestrictedSheetEquiv.mul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L371 [soft] `law-field-locker` in `structure-field RestrictedSheetEquiv.one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L372 [soft] `law-field-locker` in `structure-field RestrictedSheetEquiv.inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L425 [soft] `simp-law-injection` in `simp-declaration restrictedVolumeCharacter_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L431 [soft] `simp-law-injection` in `simp-declaration restrictedVolumeCharacter_mul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L450 [soft] `simp-law-injection` in `simp-declaration restrictedVolumeCharacter_inv` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L475 [soft] `simp-law-injection` in `simp-declaration volumeScale_pos` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L480 [soft] `simp-law-injection` in `simp-declaration volumeScale_trans` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L486 [soft] `simp-law-injection` in `simp-declaration splitWeylCharacter_fst` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L490 [soft] `simp-law-injection` in `simp-declaration splitWeylCharacter_snd` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L494 [soft] `simp-law-injection` in `simp-declaration restrictedVolumeCharacter_weylGaugeRescale` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L503 [soft] `simp-law-injection` in `simp-declaration restrictedVolumeCharacter_weylGaugeRescaleByScalar` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L521 [soft] `simp-law-injection` in `simp-declaration restrictedVolumeScale_weylGaugeRescale` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

