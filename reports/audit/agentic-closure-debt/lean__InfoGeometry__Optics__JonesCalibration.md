# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:27.961808+00:00`
Root: `lean/InfoGeometry/Optics/JonesCalibration.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **36**
- Hard: **0**
- Soft: **26**
- Advisory: **10**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Optics/JonesCalibration.lean` | `advisory` | 62 | 0 | 26 | 10 | 36 |

## Findings by file

### `lean/InfoGeometry/Optics/JonesCalibration.lean`
- module: `InfoGeometry.Optics.JonesCalibration`
- status: `advisory`
- debt_score: `62`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L85 [soft] `law-field-locker` in `structure-field SPProjectorPair.P_s_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L88 [soft] `law-field-locker` in `structure-field SPProjectorPair.P_p_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L91 [soft] `law-field-locker` in `structure-field SPProjectorPair.s_p_disjoint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L94 [soft] `law-field-locker` in `structure-field SPProjectorPair.p_s_disjoint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L97 [soft] `law-field-locker` in `structure-field SPProjectorPair.sum_eq_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L104 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L152 [soft] `law-field-locker` in `structure-field FresnelCoefficientDatum.fresnel_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L185 [soft] `law-field-locker` in `structure-field MetalBranchDatum.metal_branch_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L191 [advisory] `existential-packaging` in `def IsMetalBranch` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L216 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L258 [soft] `skeletal-proof` in `theorem R_mul_Pp_eq_zero_of_brewster` — proof appears to close via minimal tactic one-liner
  - L302 [soft] `skeletal-proof` in `theorem Pp_mul_R_eq_zero_of_brewster` — proof appears to close via minimal tactic one-liner
  - L326 [soft] `skeletal-proof` in `theorem R_mul_brewsterCoreInverse_eq_Ps` — proof appears to close via minimal tactic one-liner
  - L350 [soft] `skeletal-proof` in `theorem brewsterCoreInverse_mul_R_eq_Ps` — proof appears to close via minimal tactic one-liner
  - L384 [advisory] `local-hypothesis-injection` in `theorem one_sub_R_mul_brewsterCoreInverse_eq_Pp` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L388 [soft] `skeletal-proof` in `theorem brewsterCoreInverse_mul_Pp_eq_zero` — proof appears to close via minimal tactic one-liner
  - L422 [soft] `law-field-locker` in `structure-field BrewsterDrazinCalibration.drazin_rank_collapse_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L439 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L535 [soft] `law-field-locker` in `structure-field MetalMirrorJonesCalibration.reflectivity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L537 [soft] `law-field-locker` in `structure-field MetalMirrorJonesCalibration.retardance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L540 [soft] `law-field-locker` in `structure-field MetalMirrorJonesCalibration.ellipticity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L543 [soft] `law-field-locker` in `structure-field MetalMirrorJonesCalibration.refractiveIndex` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L546 [soft] `law-field-locker` in `structure-field MetalMirrorJonesCalibration.heat_controls_absorption_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L553 [soft] `law-field-locker` in `structure-field MetalMirrorJonesCalibration.hessian_controls_retardance_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L560 [soft] `law-field-locker` in `structure-field MetalMirrorJonesCalibration.retardance_controls_ellipticity_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L567 [soft] `law-field-locker` in `structure-field MetalMirrorJonesCalibration.refractive_index_calibration_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L586 [soft] `law-field-locker` in `structure-field V4JonesCalibration.labelOfChannel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L588 [soft] `law-field-locker` in `structure-field V4JonesCalibration.operatorOfLabel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L597 [soft] `law-field-locker` in `structure-field V4JonesCalibration.s_channel_calibrated` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L601 [soft] `law-field-locker` in `structure-field V4JonesCalibration.p_channel_calibrated` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L620 [soft] `law-field-locker` in `structure-field JonesObstructionFlow.optical_calibration_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L631 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L644 [advisory] `existential-packaging` in `def JonesCalibrationOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L654 [advisory] `existential-packaging` in `def BrewsterDrazinCalibrationOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L662 [advisory] `existential-packaging` in `def MetalMirrorJonesCalibrationOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

