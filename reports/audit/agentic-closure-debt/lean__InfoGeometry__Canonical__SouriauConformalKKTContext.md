# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:56.549532+00:00`
Root: `lean/InfoGeometry/Canonical/SouriauConformalKKTContext.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **70**
- Hard: **0**
- Soft: **52**
- Advisory: **18**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SouriauConformalKKTContext.lean` | `advisory` | 122 | 0 | 52 | 18 | 70 |

## Findings by file

### `lean/InfoGeometry/Canonical/SouriauConformalKKTContext.lean`
- module: `InfoGeometry.Canonical.SouriauConformalKKTContext`
- status: `advisory`
- debt_score: `122`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L58 [soft] `law-field-locker` in `structure-field SouriauConformalKKTContext.density` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L60 [soft] `law-field-locker` in `structure-field SouriauConformalKKTContext.hA` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L62 [soft] `law-field-locker` in `structure-field SouriauConformalKKTContext.hAMP` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L66 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L66 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L68 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L70 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L118 [soft] `skeletal-proof` in `theorem finiteUnnormalizedDensity_eq_souriauUnnormalizedDensity` — proof appears to close via minimal tactic one-liner
  - L126 [soft] `skeletal-proof` in `theorem finitePartition_eq_souriauPartition` — proof appears to close via minimal tactic one-liner
  - L133 [advisory] `existential-packaging` in `theorem finiteAdmissible` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L133 [soft] `skeletal-proof` in `theorem finiteAdmissible` — proof appears to close via minimal tactic one-liner
  - L141 [advisory] `existential-packaging` in `theorem finiteMassieu_eq_souriauMassieuPotential` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L189 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L193 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L217 [soft] `law-field-locker` in `structure-field ConformalGibbsSouriauOperatorContext.base` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L224 [soft] `law-field-locker` in `structure-field ConformalGibbsSouriauOperatorContext.readout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L228 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L228 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L298 [soft] `skeletal-proof` in `theorem operatorPartition_eq_readout_exp_neg_temperature` — proof appears to close via minimal tactic one-liner
  - L319 [soft] `skeletal-proof` in `theorem operatorMassieu_eq_log_partition` — proof appears to close via minimal tactic one-liner
  - L331 [soft] `skeletal-proof` in `theorem operatorMeanMoment_eq_readout_temperature` — proof appears to close via minimal tactic one-liner
  - L351 [soft] `skeletal-proof` in `theorem operatorConformalResponse_swap` — proof appears to close via minimal tactic one-liner
  - L368 [soft] `skeletal-proof` in `theorem conformalTemperature_eq_components` — proof appears to close via minimal tactic one-liner
  - L391 [soft] `law-field-locker` in `structure-field OperatorialWeylSupercharacterContext.gibbs` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L392 [soft] `law-field-locker` in `structure-field OperatorialWeylSupercharacterContext.bosonicReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L393 [soft] `law-field-locker` in `structure-field OperatorialWeylSupercharacterContext.fermionicReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L394 [soft] `law-field-locker` in `structure-field OperatorialWeylSupercharacterContext.readout_eq_bosonic_sub_fermionic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L399 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L399 [soft] `section-law-variable` in `variable S` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L548 [soft] `law-field-locker` in `structure-field SelfDualChiralLightConeCertificate.hGamma` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L552 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L552 [soft] `section-law-variable` in `variable S` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L589 [soft] `skeletal-proof` in `theorem spectralCommutator_mem_spectralCompact` — proof appears to close via minimal tactic one-liner
  - L647 [soft] `law-field-locker` in `structure-field ConformalPositivePartitionWitness.floor_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L649 [soft] `law-field-locker` in `structure-field ConformalPositivePartitionWitness.operatorPartition_eq_floor_add_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L684 [soft] `law-field-locker` in `structure-field ConformalCartanOddPartitionWitness.metric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L689 [soft] `law-field-locker` in `structure-field ConformalCartanOddPartitionWitness.operatorPartition_eq_cartan_floor_add_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L698 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L698 [soft] `section-law-variable` in `variable W` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L754 [soft] `law-field-locker` in `structure-field ConformalWeylTKKKKTJordanLieContext.gibbs` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L775 [soft] `law-field-locker` in `structure-field ConformalOperatorAdmissibilityWitness.gibbs` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L787 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L787 [soft] `section-law-variable` in `variable W` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L864 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L864 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L866 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L891 [soft] `skeletal-proof` in `theorem dilation_isGZero` — proof appears to close via minimal tactic one-liner
  - L913 [soft] `skeletal-proof` in `theorem circularPolarizedCommutator_isGZero` — proof appears to close via minimal tactic one-liner
  - L936 [soft] `skeletal-proof` in `theorem fockCommutator_temperature_weyl_eq_two_smul_lieProduct` — proof appears to close via minimal tactic one-liner
  - L950 [soft] `skeletal-proof` in `theorem fockAnticommutator_temperature_weyl_eq_two_smul_jordanProduct` — proof appears to close via minimal tactic one-liner
  - L1042 [soft] `skeletal-proof` in `theorem transformWeylGauge_weylTemperature` — proof appears to close via minimal tactic one-liner
  - L1095 [soft] `skeletal-proof` in `theorem fieldStrength_transformWeylGaugeByPotential_eq` — proof appears to close via minimal tactic one-liner
  - L1117 [soft] `law-field-locker` in `structure-field ConformalFisherOnsagerPositiveContext.closure` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1118 [soft] `law-field-locker` in `structure-field ConformalFisherOnsagerPositiveContext.selfResponse_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1123 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L1123 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L1134 [soft] `skeletal-proof` in `theorem fisherOnsagerProduction_nonneg` — proof appears to close via minimal tactic one-liner
  - L1160 [soft] `law-field-locker` in `structure-field ConformalSquareFisherOnsagerPositiveContext.closure` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1162 [soft] `law-field-locker` in `structure-field ConformalSquareFisherOnsagerPositiveContext.selfResponse_eq_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1168 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L1168 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L1214 [soft] `law-field-locker` in `structure-field ConformalGrandCanonicalFockContext.closure` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1220 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L1220 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L1242 [soft] `skeletal-proof` in `theorem fockOccupationOperator_eq_creation_after_annihilation` — proof appears to close via minimal tactic one-liner
  - L1251 [soft] `skeletal-proof` in `theorem chemicalPotentialFockGaugeTerm_eq_mu_smul_fockOccupation` — proof appears to close via minimal tactic one-liner
  - L1259 [soft] `skeletal-proof` in `theorem grandCanonicalFockOperator_eq_hamiltonian_sub_fockGauge` — proof appears to close via minimal tactic one-liner
  - L1299 [soft] `skeletal-proof` in `theorem finiteFockChemicalPotentialAffineFunctor_finiteGauge` — proof appears to close via minimal tactic one-liner
  - L1310 [soft] `skeletal-proof` in `theorem finiteFockChemicalPotentialAffineFunctor_fockShiftedHamiltonian` — proof appears to close via minimal tactic one-liner

