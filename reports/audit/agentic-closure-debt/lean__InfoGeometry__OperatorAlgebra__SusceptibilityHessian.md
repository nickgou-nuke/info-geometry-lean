# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:24.140409+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/SusceptibilityHessian.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **142**
- Hard: **0**
- Soft: **120**
- Advisory: **22**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/SusceptibilityHessian.lean` | `advisory` | 262 | 0 | 120 | 22 | 142 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/SusceptibilityHessian.lean`
- module: `InfoGeometry.OperatorAlgebra.SusceptibilityHessian`
- status: `advisory`
- debt_score: `262`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L38 [soft] `law-field-locker` in `structure-field HessianResponseDatum.hessian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L40 [soft] `law-field-locker` in `structure-field HessianResponseDatum.regularAt` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `law-field-locker` in `structure-field HessianResponseDatum.singularAt` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L46 [soft] `law-field-locker` in `structure-field HessianResponseDatum.singular_not_regular` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L54 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L88 [soft] `law-field-locker` in `structure-field MaterialResponseModel.frequency` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L90 [soft] `law-field-locker` in `structure-field MaterialResponseModel.incidenceAngle` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L93 [soft] `law-field-locker` in `structure-field MaterialResponseModel.complexIndex` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L96 [soft] `law-field-locker` in `structure-field MaterialResponseModel.susceptibility` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L99 [soft] `law-field-locker` in `structure-field MaterialResponseModel.material_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L110 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L128 [soft] `law-field-locker` in `structure-field HessianSusceptibilityCalibration.hessian_controls_susceptibility` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L134 [soft] `law-field-locker` in `structure-field HessianSusceptibilityCalibration.regular_response_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L138 [soft] `law-field-locker` in `structure-field HessianSusceptibilityCalibration.regular_response_valid` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L148 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L173 [soft] `law-field-locker` in `structure-field FresnelCoefficientReadout.rs` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L175 [soft] `law-field-locker` in `structure-field FresnelCoefficientReadout.rp` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L178 [soft] `law-field-locker` in `structure-field FresnelCoefficientReadout.fresnel_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L189 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L208 [soft] `law-field-locker` in `structure-field StatePolarizationEigenResponse.responseS` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L210 [soft] `law-field-locker` in `structure-field StatePolarizationEigenResponse.responseP` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L213 [soft] `law-field-locker` in `structure-field StatePolarizationEigenResponse.s_eigen_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L220 [soft] `law-field-locker` in `structure-field StatePolarizationEigenResponse.p_eigen_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L231 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L253 [soft] `law-field-locker` in `structure-field FresnelFromStateEigenResponse.rs_eq_responseS` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L256 [soft] `law-field-locker` in `structure-field FresnelFromStateEigenResponse.rp_eq_responseP` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L300 [soft] `simp-law-injection` in `simp-declaration spJonesEventOfFresnel_basis` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L307 [soft] `simp-law-injection` in `simp-declaration spJonesEventOfFresnel_coeff0` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L314 [soft] `simp-law-injection` in `simp-declaration spJonesEventOfFresnel_coeff1` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L321 [soft] `simp-law-injection` in `simp-declaration spJonesEventOfFresnel_jones_00` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L328 [soft] `simp-law-injection` in `simp-declaration spJonesEventOfFresnel_jones_11` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L343 [soft] `law-field-locker` in `structure-field JonesFromMaterialCalibration.eventOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L345 [soft] `law-field-locker` in `structure-field JonesFromMaterialCalibration.event_basis_sp` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L350 [soft] `law-field-locker` in `structure-field JonesFromMaterialCalibration.coeff0_eq_rs` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L355 [soft] `law-field-locker` in `structure-field JonesFromMaterialCalibration.coeff1_eq_rp` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L388 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L442 [soft] `law-field-locker` in `structure-field RetardanceReadout.retardance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L444 [soft] `law-field-locker` in `structure-field RetardanceReadout.ellipticity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L447 [soft] `law-field-locker` in `structure-field RetardanceReadout.retardance_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L454 [soft] `law-field-locker` in `structure-field RetardanceReadout.ellipticity_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L465 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L487 [soft] `law-field-locker` in `structure-field OpticalAbsorptionReadout.absorption` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L489 [soft] `law-field-locker` in `structure-field OpticalAbsorptionReadout.absorption_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L524 [soft] `law-field-locker` in `structure-field OpticalResponseCalibration.hessian_controls_optical_response` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L531 [soft] `law-field-locker` in `structure-field OpticalResponseCalibration.absorption_matches_bregman_heat` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L576 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L658 [soft] `law-field-locker` in `structure-field OpticalResponseEigenCalibration.hessian_controls_optical_response` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L665 [soft] `law-field-locker` in `structure-field OpticalResponseEigenCalibration.absorption_matches_bregman_heat` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L672 [soft] `law-field-locker` in `structure-field OpticalResponseEigenCalibration.hessian_controls_retardance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L746 [soft] `law-field-locker` in `structure-field InformationPotentialDatum.potential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L748 [soft] `law-field-locker` in `structure-field InformationPotentialDatum.hessian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L751 [soft] `law-field-locker` in `structure-field InformationPotentialDatum.symmetric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L755 [soft] `law-field-locker` in `structure-field InformationPotentialDatum.positive_semidefinite` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L763 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L789 [soft] `law-field-locker` in `structure-field BregmanHeatDatum.heat` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L791 [soft] `law-field-locker` in `structure-field BregmanHeatDatum.nonnegative` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L795 [soft] `law-field-locker` in `structure-field BregmanHeatDatum.zero_on_diagonal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L803 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L827 [soft] `law-field-locker` in `structure-field LinearSusceptibilityDatum.susceptibility` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L829 [soft] `law-field-locker` in `structure-field LinearSusceptibilityDatum.causal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L832 [soft] `law-field-locker` in `structure-field LinearSusceptibilityDatum.linearResponseOrigin` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L835 [soft] `law-field-locker` in `structure-field LinearSusceptibilityDatum.hessianCompatibility` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L857 [soft] `law-field-locker` in `structure-field HessianSusceptibilityBridge.tangentOfPerturbation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L860 [soft] `law-field-locker` in `structure-field HessianSusceptibilityBridge.susceptibility_eq_hessian_response` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L871 [soft] `law-field-locker` in `structure-field DielectricResponseDatum.epsilon` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L873 [soft] `law-field-locker` in `structure-field DielectricResponseDatum.mu` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L876 [soft] `law-field-locker` in `structure-field DielectricResponseDatum.refractiveIndex` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L879 [soft] `law-field-locker` in `structure-field DielectricResponseDatum.impedance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L882 [soft] `law-field-locker` in `structure-field DielectricResponseDatum.opticalBackendValid` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L885 [soft] `law-field-locker` in `structure-field DielectricResponseDatum.fromSusceptibility` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L902 [soft] `law-field-locker` in `structure-field OpticalInterfaceResponse.n1` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L904 [soft] `law-field-locker` in `structure-field OpticalInterfaceResponse.n2` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L907 [soft] `law-field-locker` in `structure-field OpticalInterfaceResponse.cosIncident` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L910 [soft] `law-field-locker` in `structure-field OpticalInterfaceResponse.cosTransmitted` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L913 [soft] `law-field-locker` in `structure-field OpticalInterfaceResponse.interfaceGeometryValid` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L944 [soft] `law-field-locker` in `structure-field MaterialFresnelCoefficientDatum.r_s` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L947 [soft] `law-field-locker` in `structure-field MaterialFresnelCoefficientDatum.r_p` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L950 [soft] `law-field-locker` in `structure-field MaterialFresnelCoefficientDatum.t_s` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L953 [soft] `law-field-locker` in `structure-field MaterialFresnelCoefficientDatum.t_p` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L956 [soft] `law-field-locker` in `structure-field MaterialFresnelCoefficientDatum.r_s_eq_standard` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L960 [soft] `law-field-locker` in `structure-field MaterialFresnelCoefficientDatum.r_p_eq_standard` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L964 [soft] `law-field-locker` in `structure-field MaterialFresnelCoefficientDatum.transmissionBoundaryLaw` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L971 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L995 [soft] `law-field-locker` in `structure-field PolarizationEigenResponse.eigenvalue` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1013 [soft] `law-field-locker` in `structure-field FresnelEigenCalibration.s_eigenvalue_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1019 [soft] `law-field-locker` in `structure-field FresnelEigenCalibration.p_eigenvalue_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1029 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L1066 [soft] `law-field-locker` in `structure-field OperatorialJonesResponse.jonesOperator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1068 [soft] `law-field-locker` in `structure-field OperatorialJonesResponse.operatorialBoundaryLaw` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1082 [soft] `law-field-locker` in `structure-field JonesFresnelCalibration.sCalibration` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1085 [soft] `law-field-locker` in `structure-field JonesFresnelCalibration.pCalibration` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1088 [soft] `law-field-locker` in `structure-field JonesFresnelCalibration.fluxAccounting` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1110 [soft] `law-field-locker` in `structure-field SusceptibilityHessianFresnelBridge.dielectric_from_hessian_susceptibility` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1113 [soft] `law-field-locker` in `structure-field SusceptibilityHessianFresnelBridge.fresnel_from_dielectric_response` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1155 [soft] `law-field-locker` in `structure-field OpticalStinespringHeatCalibration.stateToSystem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1158 [soft] `law-field-locker` in `structure-field OpticalStinespringHeatCalibration.absorptionFromState` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1166 [soft] `law-field-locker` in `structure-field OpticalStinespringHeatCalibration.absorption_eq_heat` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1185 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L1225 [soft] `law-field-locker` in `structure-field OpticalPTStinespringClinch.eventOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1229 [soft] `law-field-locker` in `structure-field OpticalPTStinespringClinch.event_tag_pt` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1233 [soft] `law-field-locker` in `structure-field OpticalPTStinespringClinch.pt_commutant_sector_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1250 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L1336 [soft] `law-field-locker` in `structure-field BregmanHessianResponse.hessianAt` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1338 [soft] `law-field-locker` in `structure-field BregmanHessianResponse.symmetric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1342 [soft] `law-field-locker` in `structure-field BregmanHessianResponse.nonnegative` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1346 [soft] `law-field-locker` in `structure-field BregmanHessianResponse.bregman_hessian_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1357 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L1388 [soft] `law-field-locker` in `structure-field SusceptibilityDatum.susceptibility` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1390 [soft] `law-field-locker` in `structure-field SusceptibilityDatum.susceptibility_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1406 [soft] `law-field-locker` in `structure-field StateDielectricResponseDatum.epsilon` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1408 [soft] `law-field-locker` in `structure-field StateDielectricResponseDatum.mu` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1411 [soft] `law-field-locker` in `structure-field StateDielectricResponseDatum.dielectric_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1426 [soft] `law-field-locker` in `structure-field ComplexRefractiveIndexDatum.N` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1428 [soft] `law-field-locker` in `structure-field ComplexRefractiveIndexDatum.refractive_index_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1452 [soft] `law-field-locker` in `structure-field BregmanHessianSusceptibilityCalibration.hessian_controls_susceptibility_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1467 [soft] `law-field-locker` in `structure-field FresnelFromRefractiveIndex.coeff_s` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1469 [soft] `law-field-locker` in `structure-field FresnelFromRefractiveIndex.coeff_p` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1472 [soft] `law-field-locker` in `structure-field FresnelFromRefractiveIndex.fresnel_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1487 [soft] `law-field-locker` in `structure-field OpticalResponseEigenvalues.eigenvalue` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1492 [soft] `law-field-locker` in `structure-field OpticalResponseEigenvalues.eigenvalue_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1528 [soft] `law-field-locker` in `structure-field SusceptibilityFresnelCalibration.coeff_s_eq_eigen_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1534 [soft] `law-field-locker` in `structure-field SusceptibilityFresnelCalibration.coeff_p_eq_eigen_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1540 [soft] `law-field-locker` in `structure-field SusceptibilityFresnelCalibration.end_to_end_optical_response_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1553 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L1597 [soft] `law-field-locker` in `structure-field HessianJonesCalibration.tagOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1600 [soft] `law-field-locker` in `structure-field HessianJonesCalibration.coherence_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1603 [soft] `law-field-locker` in `structure-field HessianJonesCalibration.coherent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1614 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L1631 [soft] `skeletal-proof` in `theorem event_coeff0_eq_fresnel_s` — proof appears to close via minimal tactic one-liner
  - L1643 [soft] `skeletal-proof` in `theorem event_coeff1_eq_fresnel_p` — proof appears to close via minimal tactic one-liner
  - L1655 [soft] `skeletal-proof` in `theorem event_coeff0_eq_response_eigenvalue` — proof appears to close via minimal tactic one-liner
  - L1670 [soft] `skeletal-proof` in `theorem event_coeff1_eq_response_eigenvalue` — proof appears to close via minimal tactic one-liner
  - L1698 [soft] `law-field-locker` in `structure-field MetalMirrorSusceptibilityCalibration.metal_mirror_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1705 [soft] `law-field-locker` in `structure-field MetalMirrorSusceptibilityCalibration.absorption_heat_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1712 [soft] `law-field-locker` in `structure-field MetalMirrorSusceptibilityCalibration.retardance_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1725 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L1759 [soft] `law-field-locker` in `structure-field VacuumResponseCalibration.vacuum_susceptibility_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1779 [soft] `law-field-locker` in `structure-field MatterResponseCalibration.matter_response_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1786 [advisory] `existential-packaging` in `def MaterialSusceptibilityHessianCompatibility` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1796 [advisory] `existential-packaging` in `def MaterialSusceptibilityHessianOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1807 [advisory] `existential-packaging` in `def SusceptibilityHessianOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

