# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:47.559599+00:00`
Root: `lean/InfoGeometry/Thermo/SusceptibilityHessian.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **63**
- Hard: **0**
- Soft: **49**
- Advisory: **14**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Thermo/SusceptibilityHessian.lean` | `advisory` | 112 | 0 | 49 | 14 | 63 |

## Findings by file

### `lean/InfoGeometry/Thermo/SusceptibilityHessian.lean`
- module: `InfoGeometry.Thermo.SusceptibilityHessian`
- status: `advisory`
- debt_score: `112`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L37 [soft] `law-field-locker` in `structure-field HessianResponseDatum.hessian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L39 [soft] `law-field-locker` in `structure-field HessianResponseDatum.fieldReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L42 [soft] `law-field-locker` in `structure-field HessianResponseDatum.responseReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L45 [soft] `law-field-locker` in `structure-field HessianResponseDatum.hessian_response_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L60 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L83 [soft] `law-field-locker` in `structure-field SusceptibilityDatum.susceptibility` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L85 [soft] `law-field-locker` in `structure-field SusceptibilityDatum.derived_from_hessian_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L99 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L129 [soft] `law-field-locker` in `structure-field ConstructiveHessianSusceptibilityCalibration.fieldToTangent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L133 [soft] `law-field-locker` in `structure-field ConstructiveHessianSusceptibilityCalibration.responseFromTangent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L145 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L158 [soft] `skeletal-proof` in `theorem susceptibility_eq_hessian_response` — proof appears to close via minimal tactic one-liner
  - L166 [soft] `skeletal-proof` in `theorem susceptibility_apply` — proof appears to close via minimal tactic one-liner
  - L192 [soft] `skeletal-proof` in `theorem toSusceptibilityDatum_susceptibility` — proof appears to close via minimal tactic one-liner
  - L197 [soft] `skeletal-proof` in `theorem toSusceptibilityDatum_derived_from_hessian` — proof appears to close via minimal tactic one-liner
  - L219 [soft] `law-field-locker` in `structure-field DielectricResponseDatum.epsilon` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L221 [soft] `law-field-locker` in `structure-field DielectricResponseDatum.refractiveIndex` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L224 [soft] `law-field-locker` in `structure-field DielectricResponseDatum.refractive_index_calibration_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L233 [soft] `law-field-locker` in `structure-field DielectricResponseDatum.susceptibility_to_epsilon_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L244 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L267 [soft] `law-field-locker` in `structure-field ConstructiveDielectricResponseCalibration.epsilon` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L269 [soft] `law-field-locker` in `structure-field ConstructiveDielectricResponseCalibration.refractiveIndex` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L272 [soft] `law-field-locker` in `structure-field ConstructiveDielectricResponseCalibration.susceptibilityEpsilonReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L275 [soft] `law-field-locker` in `structure-field ConstructiveDielectricResponseCalibration.refractive_index_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L279 [soft] `law-field-locker` in `structure-field ConstructiveDielectricResponseCalibration.epsilon_eq_susceptibility_readout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L287 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L303 [soft] `skeletal-proof` in `theorem toDielectricResponseDatum_epsilon` — proof appears to close via minimal tactic one-liner
  - L308 [soft] `skeletal-proof` in `theorem toDielectricResponseDatum_refractiveIndex` — proof appears to close via minimal tactic one-liner
  - L343 [soft] `law-field-locker` in `structure-field OpticalInterfaceGeometry.angle_calibration_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L352 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L378 [soft] `law-field-locker` in `structure-field FresnelFromSusceptibilityCalibration.fresnel_from_dielectric_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L392 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L418 [soft] `law-field-locker` in `structure-field SPEigenResponseCalibration.responseOp` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L420 [soft] `law-field-locker` in `structure-field SPEigenResponseCalibration.eigenvalue` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L423 [soft] `law-field-locker` in `structure-field SPEigenResponseCalibration.s_eigen` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L429 [soft] `law-field-locker` in `structure-field SPEigenResponseCalibration.p_eigen` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L441 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L484 [soft] `law-field-locker` in `structure-field FresnelEigenvalueCalibration.coeffs` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L486 [soft] `law-field-locker` in `structure-field FresnelEigenvalueCalibration.coeff_s` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L491 [soft] `law-field-locker` in `structure-field FresnelEigenvalueCalibration.coeff_p` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L496 [soft] `law-field-locker` in `structure-field FresnelEigenvalueCalibration.fresnel_boundary_calibration_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L510 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L603 [soft] `law-field-locker` in `structure-field MetalMirrorSusceptibilityCalibration.hessian_controls_susceptibility_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L610 [soft] `law-field-locker` in `structure-field MetalMirrorSusceptibilityCalibration.susceptibility_controls_absorption_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L617 [soft] `law-field-locker` in `structure-field MetalMirrorSusceptibilityCalibration.susceptibility_controls_retardance_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L624 [soft] `law-field-locker` in `structure-field MetalMirrorSusceptibilityCalibration.jones_calibrated_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L639 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L718 [soft] `law-field-locker` in `structure-field SusceptibilityHessianJonesCalibration.hessian_controls_susceptibility_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L725 [soft] `law-field-locker` in `structure-field SusceptibilityHessianJonesCalibration.susceptibility_controls_dielectric_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L732 [soft] `law-field-locker` in `structure-field SusceptibilityHessianJonesCalibration.dielectric_controls_fresnel_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L739 [soft] `law-field-locker` in `structure-field SusceptibilityHessianJonesCalibration.jones_calibrated_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L821 [soft] `law-field-locker` in `structure-field MetalMirrorSusceptibilityHessianCalibration.absorption` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L824 [soft] `law-field-locker` in `structure-field MetalMirrorSusceptibilityHessianCalibration.retardance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L827 [soft] `law-field-locker` in `structure-field MetalMirrorSusceptibilityHessianCalibration.ellipticity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L830 [soft] `law-field-locker` in `structure-field MetalMirrorSusceptibilityHessianCalibration.complexIndex` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L833 [soft] `law-field-locker` in `structure-field MetalMirrorSusceptibilityHessianCalibration.response_controls_absorption_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L840 [soft] `law-field-locker` in `structure-field MetalMirrorSusceptibilityHessianCalibration.eigenphase_controls_retardance_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L847 [soft] `law-field-locker` in `structure-field MetalMirrorSusceptibilityHessianCalibration.eigenresponse_controls_ellipticity_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L854 [soft] `law-field-locker` in `structure-field MetalMirrorSusceptibilityHessianCalibration.complex_index_calibrated_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L915 [advisory] `existential-packaging` in `def MetalMirrorSusceptibilityCalibrationOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L929 [advisory] `existential-packaging` in `def SusceptibilityHessianOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L941 [advisory] `existential-packaging` in `def MetalMirrorSusceptibilityHessianOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

