# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:20.019675+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/OperatorThermodynamics.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **127**
- Hard: **0**
- Soft: **88**
- Advisory: **39**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/OperatorThermodynamics.lean` | `advisory` | 215 | 0 | 88 | 39 | 127 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/OperatorThermodynamics.lean`
- module: `InfoGeometry.OperatorAlgebra.OperatorThermodynamics`
- status: `advisory`
- debt_score: `215`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L42 [soft] `law-field-locker` in `structure-field AlgebraicState.eval` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L44 [soft] `law-field-locker` in `structure-field AlgebraicState.state_certificates` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [soft] `law-field-locker` in `structure-field OperatorFlow.flow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L57 [soft] `law-field-locker` in `structure-field OperatorFlow.flow_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L61 [soft] `law-field-locker` in `structure-field OperatorFlow.flow_add` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L65 [soft] `law-field-locker` in `structure-field OperatorFlow.multiplicative` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L72 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L73 [soft] `simp-law-injection` in `simp-declaration flow_zero_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L103 [soft] `law-field-locker` in `structure-field KMSState.flow_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L107 [soft] `law-field-locker` in `structure-field KMSState.kms_boundary_condition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L128 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L155 [soft] `law-field-locker` in `structure-field StateRestriction.includeMap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L163 [soft] `law-field-locker` in `structure-field StateRestriction.restrict_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L172 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L193 [soft] `law-field-locker` in `structure-field FinitePartialTraceShadow.partialTrace` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L196 [soft] `law-field-locker` in `structure-field FinitePartialTraceShadow.partialTrace_agrees_with_restriction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L214 [soft] `law-field-locker` in `structure-field KMSAnalyticBoundary.boundaryCondition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L233 [soft] `law-field-locker` in `structure-field ObserverReduction.globalEval` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L235 [soft] `law-field-locker` in `structure-field ObserverReduction.observableEval` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L238 [soft] `law-field-locker` in `structure-field ObserverReduction.agrees_on_observable` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L242 [soft] `law-field-locker` in `structure-field ObserverReduction.commutant_inaccessible_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L249 [soft] `law-field-locker` in `structure-field ObserverReduction.reduction_backend_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L252 [advisory] `witness-field-projection` in `structure-field reduction_backend_valid` — witness field `reduction_backend_valid : reduction_backend_law` detected; verify owner-level derivation
  - L261 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L289 [soft] `law-field-locker` in `structure-field TomitaKMSThermalization.thermal_eq_reduction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L293 [soft] `law-field-locker` in `structure-field TomitaKMSThermalization.modular_origin_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L300 [soft] `law-field-locker` in `structure-field TomitaKMSThermalization.horizon_or_wedge_origin_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L314 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L315 [advisory] `existential-packaging` in `theorem exists_kms_state_for_observer` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L369 [soft] `law-field-locker` in `structure-field HorizonCommutantBoundary.boundary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L371 [soft] `law-field-locker` in `structure-field HorizonCommutantBoundary.boundary_maps_observable_to_commutant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L375 [soft] `law-field-locker` in `structure-field HorizonCommutantBoundary.boundary_is_defect_locus_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L406 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L414 [advisory] `existential-packaging` in `theorem observer_sees_kms` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L447 [soft] `law-field-locker` in `structure-field ModularKMSDatum.tomita_takesaki_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L467 [soft] `law-field-locker` in `structure-field HorizonFlowCalibration.modular_eq_physical_after_rescaling` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L473 [soft] `law-field-locker` in `structure-field HorizonFlowCalibration.geometric_calibration_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L500 [soft] `law-field-locker` in `structure-field EmergentThermalRadiation.beta_calibration` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L510 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L516 [advisory] `existential-packaging` in `theorem has_modular_kms_state` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L537 [soft] `law-field-locker` in `structure-field KMSCondition.flow_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L540 [soft] `law-field-locker` in `structure-field KMSCondition.analyticStrip` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L543 [soft] `law-field-locker` in `structure-field KMSCondition.boundaryRelation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L556 [soft] `law-field-locker` in `structure-field BipartiteTomitaState.eval` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L558 [soft] `law-field-locker` in `structure-field BipartiteTomitaState.state_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L561 [soft] `law-field-locker` in `structure-field BipartiteTomitaState.tomita_pair_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L574 [soft] `law-field-locker` in `structure-field AccessibleRestrictionDatum.restrict` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L576 [soft] `law-field-locker` in `structure-field AccessibleRestrictionDatum.observable_domain` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L580 [soft] `law-field-locker` in `structure-field AccessibleRestrictionDatum.restrictionCertificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L583 [advisory] `existential-packaging` in `structure ModularThermalizationWitness` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L602 [soft] `law-field-locker` in `structure-field ModularThermalizationWitness.restriction_is_kms` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L613 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L614 [advisory] `existential-packaging` in `theorem observer_restriction_is_kms` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L638 [soft] `law-field-locker` in `structure-field HawkingKMSReadoutDatum.surfaceGravity_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L642 [soft] `law-field-locker` in `structure-field HawkingKMSReadoutDatum.hawkingBetaLaw` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L646 [soft] `law-field-locker` in `structure-field HawkingKMSReadoutDatum.geometricHorizonFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L649 [soft] `law-field-locker` in `structure-field HawkingKMSReadoutDatum.radiationInterpretation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L657 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L658 [advisory] `existential-packaging` in `theorem observer_restriction_is_kms` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L678 [soft] `law-field-locker` in `structure-field KleinianThermodynamicCompatibility.tomita_cartan` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L680 [soft] `law-field-locker` in `structure-field KleinianThermodynamicCompatibility.kleinian_twist` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L687 [soft] `law-field-locker` in `structure-field KleinianThermodynamicCompatibility.compatibility` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L701 [advisory] `bridge-shaped-declaration` in `theorem ModularThermodynamicsOwnerTarget.witness_law` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L701 [advisory] `existential-packaging` in `theorem ModularThermodynamicsOwnerTarget.witness_law` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L713 [advisory] `bridge-shaped-declaration` in `theorem EmergentThermalRadiationOwnerTarget.witness_law` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L713 [advisory] `existential-packaging` in `theorem EmergentThermalRadiationOwnerTarget.witness_law` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L735 [advisory] `existential-packaging` in `structure TomitaKMSThermalizationOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L772 [advisory] `existential-packaging` in `structure HorizonKMSThermodynamicsOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L810 [soft] `law-field-locker` in `structure-field FlowDatum.flow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L812 [soft] `law-field-locker` in `structure-field FlowDatum.flow_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L816 [soft] `law-field-locker` in `structure-field FlowDatum.flow_add` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L824 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L825 [soft] `simp-law-injection` in `simp-declaration flow_zero_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L851 [soft] `law-field-locker` in `structure-field ModularFlow.flow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L853 [soft] `law-field-locker` in `structure-field ModularFlow.flow_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L857 [soft] `law-field-locker` in `structure-field ModularFlow.flow_add` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L865 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L866 [soft] `simp-law-injection` in `simp-declaration flow_zero_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L902 [soft] `law-field-locker` in `structure-field StateFunctional.eval` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L904 [soft] `law-field-locker` in `structure-field StateFunctional.positive` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L907 [soft] `law-field-locker` in `structure-field StateFunctional.normalized` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L910 [soft] `law-field-locker` in `structure-field StateFunctional.normality` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L927 [soft] `law-field-locker` in `structure-field KMSAnalyticCertificate.boundaryCondition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L945 [soft] `law-field-locker` in `structure-field KMSState.flow_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L958 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L988 [soft] `law-field-locker` in `structure-field KMSAnalyticBoundary.boundaryCondition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1014 [soft] `law-field-locker` in `structure-field TomitaKMSDatum.faithfulNormal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1017 [soft] `law-field-locker` in `structure-field TomitaKMSDatum.tomitaModularFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1020 [soft] `law-field-locker` in `structure-field TomitaKMSDatum.modular_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1033 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L1041 [soft] `simp-law-injection` in `simp-declaration toKMSState_eval` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1043 [soft] `skeletal-proof` in `theorem toKMSState_eval` — proof appears to close via minimal tactic one-liner
  - L1065 [soft] `law-field-locker` in `structure-field ObservableRestrictionDatum.embedVisible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1073 [soft] `law-field-locker` in `structure-field ObservableRestrictionDatum.visible_eq_restriction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1078 [soft] `law-field-locker` in `structure-field ObservableRestrictionDatum.hiddenSectorInaccessible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1085 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L1108 [soft] `law-field-locker` in `structure-field ObserverReduction.globalEval` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1110 [soft] `law-field-locker` in `structure-field ObserverReduction.observableEval` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1113 [soft] `law-field-locker` in `structure-field ObserverReduction.agrees_on_observable` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1117 [soft] `law-field-locker` in `structure-field ObserverReduction.commutant_inaccessible_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1124 [soft] `law-field-locker` in `structure-field ObserverReduction.reduction_backend_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1131 [advisory] `witness-field-projection` in `structure-field reduction_backend_valid` — witness field `reduction_backend_valid : reduction_backend_law` detected; verify owner-level derivation
  - L1140 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L1170 [soft] `law-field-locker` in `structure-field TomitaKMSThermalization.thermal_eq_reduction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1174 [soft] `law-field-locker` in `structure-field TomitaKMSThermalization.modular_origin_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1181 [soft] `law-field-locker` in `structure-field TomitaKMSThermalization.horizon_or_wedge_origin_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1195 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L1196 [advisory] `existential-packaging` in `theorem exists_kms_state_for_observer` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1210 [soft] `skeletal-proof` in `theorem reduced_state_flow_invariant` — proof appears to close via minimal tactic one-liner
  - L1251 [soft] `law-field-locker` in `structure-field HorizonCommutantBoundary.boundary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1253 [soft] `law-field-locker` in `structure-field HorizonCommutantBoundary.boundary_maps_observable_to_commutant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1257 [soft] `law-field-locker` in `structure-field HorizonCommutantBoundary.boundary_is_defect_locus_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1290 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L1298 [advisory] `existential-packaging` in `theorem observer_sees_kms` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1339 [soft] `law-field-locker` in `structure-field ObservableKMSReduction.kms_eval_eq_visible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1345 [soft] `law-field-locker` in `structure-field ObservableKMSReduction.tomitaReductionCertificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1352 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L1390 [soft] `law-field-locker` in `structure-field HorizonThermalCalibration.modularFlow_is_horizon_time` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1393 [soft] `law-field-locker` in `structure-field HorizonThermalCalibration.KMS_is_hawking_unruh_readout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1407 [soft] `law-field-locker` in `structure-field HawkingUnruhBranch.beta_matches` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1415 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L1442 [soft] `law-field-locker` in `structure-field TypeIPartialTraceDatum.partialTraceHidden` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1445 [soft] `law-field-locker` in `structure-field TypeIPartialTraceDatum.isTypeIPartialTrace` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1448 [advisory] `existential-packaging` in `structure TomitaKMSOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1507 [advisory] `existential-packaging` in `structure TomitaKMSThermalizationOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1544 [advisory] `existential-packaging` in `structure HorizonKMSThermodynamicsOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

