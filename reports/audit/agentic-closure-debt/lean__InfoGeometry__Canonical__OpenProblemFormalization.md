# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:34.887154+00:00`
Root: `lean/InfoGeometry/Canonical/OpenProblemFormalization.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **110**
- Hard: **0**
- Soft: **99**
- Advisory: **11**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/OpenProblemFormalization.lean` | `advisory` | 209 | 0 | 99 | 11 | 110 |

## Findings by file

### `lean/InfoGeometry/Canonical/OpenProblemFormalization.lean`
- module: `InfoGeometry.Canonical.OpenProblemFormalization`
- status: `advisory`
- debt_score: `209`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L45 [soft] `law-field-locker` in `structure-field FrontierHypotheses.V4_Weyl_Isomorphism` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L46 [soft] `law-field-locker` in `structure-field FrontierHypotheses.V4_symmetry_forces_compactification` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [soft] `law-field-locker` in `structure-field FrontierHypotheses.microscopic_V4_induces_partition_modularity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L48 [soft] `law-field-locker` in `structure-field FrontierHypotheses.DrazinCore_BPS_Correspondence` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [soft] `law-field-locker` in `structure-field FrontierHypotheses.DrazinCore_zero_entropy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L50 [soft] `law-field-locker` in `structure-field FrontierHypotheses.DiracDrazin_well_posedness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [soft] `law-field-locker` in `structure-field FrontierHypotheses.m_eff_anomaly_lock` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [soft] `law-field-locker` in `structure-field FrontierHypotheses.SouriauDiracDrazin_equivalence` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L53 [soft] `law-field-locker` in `structure-field FrontierHypotheses.Souriau_KMS_BPS_Correspondence` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L54 [soft] `law-field-locker` in `structure-field FrontierHypotheses.souriau_equilibrium_implies_riemann_zeros` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [soft] `law-field-locker` in `structure-field FrontierHypotheses.Ternaform_conformal_closure` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L56 [soft] `law-field-locker` in `structure-field FrontierHypotheses.ConformalClosure_compact` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L57 [soft] `law-field-locker` in `structure-field FrontierHypotheses.ternaform_closure_yields_riemann_resonances` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L58 [soft] `law-field-locker` in `structure-field FrontierHypotheses.Fierz_spacetime_emergence` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L59 [soft] `law-field-locker` in `structure-field FrontierHypotheses.Fierz_vector_equals_Souriau_temperature` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L60 [soft] `law-field-locker` in `structure-field FrontierHypotheses.gravity_as_thermal_viscosity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L61 [soft] `law-field-locker` in `structure-field FrontierHypotheses.lie_orbit_quantization` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L62 [soft] `law-field-locker` in `structure-field FrontierHypotheses.spinorial_mellin_transform_has_riemann_spectrum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L63 [soft] `law-field-locker` in `structure-field FrontierHypotheses.modular_inversion_forces_critical_line` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L64 [soft] `law-field-locker` in `structure-field FrontierHypotheses.Riemann_BPS_Correspondence` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L65 [soft] `law-field-locker` in `structure-field FrontierHypotheses.MaxEnt_RH_Equivalence` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L66 [soft] `law-field-locker` in `structure-field FrontierHypotheses.arithmetic_cosmological_stability` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [soft] `law-field-locker` in `structure-field FrontierHypotheses.Spire_Stability_Unification` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [soft] `law-field-locker` in `structure-field FrontierHypotheses.CollisionResistance_RH` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L69 [soft] `law-field-locker` in `structure-field FrontierHypotheses.identity_preserved` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L70 [soft] `law-field-locker` in `structure-field FrontierHypotheses.FTA_RH_topological_equivalence` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L71 [soft] `law-field-locker` in `structure-field FrontierHypotheses.dark_energy_is_modular_remainder` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L72 [soft] `law-field-locker` in `structure-field FrontierHypotheses.dark_energy_density_scaling` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L73 [soft] `law-field-locker` in `structure-field FrontierHypotheses.central_charge_calibration` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L74 [soft] `law-field-locker` in `structure-field FrontierHypotheses.dark_energy_prevents_collision` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L75 [soft] `law-field-locker` in `structure-field FrontierHypotheses.arithmetic_big_bang_is_bayesian_update` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L76 [soft] `law-field-locker` in `structure-field FrontierHypotheses.MoebiusV4_dark_matter_dark_energy_swap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L103 [soft] `vacuous-prop` in `prop <vacuous>` — Prop declaration appears to reduce to True/False
  - L128 [soft] `vacuous-prop` in `prop <vacuous>` — Prop declaration appears to reduce to True/False
  - L129 [advisory] `bridge-shaped-declaration` in `def concrete_real_pfaffian_bridge` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L129 [soft] `vacuous-prop` in `prop <vacuous>` — Prop declaration appears to reduce to True/False
  - L134 [soft] `law-field-locker` in `structure-field PrimeGasSymmetry.V4_iso` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L138 [soft] `vacuous-prop` in `prop <vacuous>` — Prop declaration appears to reduce to True/False
  - L142 [soft] `law-field-locker` in `structure-field FierzStressProjectionContext.projection` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L148 [soft] `skeletal-proof` in `theorem projectedStress_fierz_identity` — proof appears to close via minimal tactic one-liner
  - L148 [soft] `vacuous-prop` in `prop <vacuous>` — Prop declaration appears to reduce to True/False
  - L150 [soft] `skeletal-proof` in `theorem projectedStress_majorana_identity` — proof appears to close via minimal tactic one-liner
  - L160 [soft] `law-field-locker` in `structure-field OnsagerReciprocalFlow.symmetry` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L164 [soft] `law-field-locker` in `structure-field PrimeGasOnsagerFierzBridge.eulerProductHypothesis` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L165 [soft] `law-field-locker` in `structure-field PrimeGasOnsagerFierzBridge.primeLogEnergyHypothesis` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L166 [soft] `skeletal-proof` in `theorem onsager_projectedStress_fierz_identity` — proof appears to close via minimal tactic one-liner
  - L172 [soft] `law-field-locker` in `structure-field PrimeGasKMSTargetBridge.betaOdd_eq_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L173 [soft] `vacuous-prop` in `prop <vacuous>` — Prop declaration appears to reduce to True/False
  - L175 [soft] `skeletal-proof` in `theorem toSuperGeometricTemperature_zero_odd` — proof appears to close via minimal tactic one-liner
  - L177 [soft] `skeletal-proof` in `theorem kms_target_projectedStress_fierz_identity` — proof appears to close via minimal tactic one-liner
  - L185 [soft] `law-field-locker` in `structure-field ModularDerivationTower.tower` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L193 [soft] `law-field-locker` in `structure-field HigherOrderOnsagerOperatorialTheory.entropyProduction_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L195 [soft] `skeletal-proof` in `theorem higher_order_projectedStress_fierz_identity` — proof appears to close via minimal tactic one-liner
  - L195 [soft] `vacuous-prop` in `prop <vacuous>` — Prop declaration appears to reduce to True/False
  - L205 [soft] `vacuous-prop` in `prop <vacuous>` — Prop declaration appears to reduce to True/False
  - L210 [soft] `vacuous-prop` in `prop <vacuous>` — Prop declaration appears to reduce to True/False
  - L220 [soft] `law-field-locker` in `structure-field ClosedOperatorDatum.op` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L240 [advisory] `existential-packaging` in `def ReducesBounded` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L266 [soft] `law-field-locker` in `structure-field RelativeSpectralSetHypotheses.radius_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L267 [soft] `law-field-locker` in `structure-field RelativeSpectralSetHypotheses.sigma_norm_le` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L269 [soft] `law-field-locker` in `structure-field RelativeSpectralSetHypotheses.xi_large` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L270 [soft] `law-field-locker` in `structure-field RelativeSpectralSetHypotheses.spectralSetOfExtendedSpectrum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L272 [soft] `law-field-locker` in `structure-field RelativeSpectralSetHypotheses.Gamma0_admissible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L273 [soft] `vacuous-prop` in `prop <vacuous>` — Prop declaration appears to reduce to True/False
  - L280 [soft] `vacuous-prop` in `prop <vacuous>` — Prop declaration appears to reduce to True/False
  - L287 [soft] `vacuous-prop` in `prop <vacuous>` — Prop declaration appears to reduce to True/False
  - L294 [soft] `vacuous-prop` in `prop <vacuous>` — Prop declaration appears to reduce to True/False
  - L301 [soft] `vacuous-prop` in `prop <vacuous>` — Prop declaration appears to reduce to True/False
  - L308 [soft] `vacuous-prop` in `prop <vacuous>` — Prop declaration appears to reduce to True/False
  - L321 [soft] `law-field-locker` in `structure-field KolihaZeroBranchHypotheses.zeroNotAccumulation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L322 [soft] `law-field-locker` in `structure-field KolihaZeroBranchHypotheses.coreBoundedAwayFromZero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L323 [soft] `law-field-locker` in `structure-field KolihaZeroBranchHypotheses.spectralSetOfExtendedSpectrum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L325 [soft] `law-field-locker` in `structure-field KolihaZeroBranchHypotheses.GammaZero_admissible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L327 [soft] `law-field-locker` in `structure-field KolihaZeroBranchHypotheses.GammaCore_admissibleInRiemannSphere` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L334 [soft] `law-field-locker` in `structure-field RelativeSpectralDrazinSurgeryWitness.Pcore` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L339 [soft] `law-field-locker` in `structure-field RelativeSpectralDrazinSurgeryWitness.Pcore_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L341 [soft] `law-field-locker` in `structure-field RelativeSpectralDrazinSurgeryWitness.Pcore_idempotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L343 [soft] `law-field-locker` in `structure-field RelativeSpectralDrazinSurgeryWitness.complementary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L345 [soft] `law-field-locker` in `structure-field RelativeSpectralDrazinSurgeryWitness.disjoint_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L347 [soft] `law-field-locker` in `structure-field RelativeSpectralDrazinSurgeryWitness.disjoint_right` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L376 [soft] `law-field-locker` in `structure-field RelativeSpectralDrazinSurgeryWitness.projection_identity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L380 [advisory] `existential-packaging` in `def RelativeSpectralDrazinSurgery` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L396 [soft] `law-field-locker` in `structure-field StrictKolihaDrazinSingletonSurgeryWitness.sigma_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L402 [advisory] `existential-packaging` in `def StrictKolihaDrazinSingletonSurgery` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L416 [soft] `law-field-locker` in `structure-field KolihaDrazinSurgeryWitness.Pnil` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L417 [soft] `law-field-locker` in `structure-field KolihaDrazinSurgeryWitness.Pcore` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L418 [soft] `law-field-locker` in `structure-field KolihaDrazinSurgeryWitness.AD` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L419 [soft] `law-field-locker` in `structure-field KolihaDrazinSurgeryWitness.Anil` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L420 [soft] `law-field-locker` in `structure-field KolihaDrazinSurgeryWitness.Pcore_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L422 [soft] `law-field-locker` in `structure-field KolihaDrazinSurgeryWitness.Pnil_idempotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L424 [soft] `law-field-locker` in `structure-field KolihaDrazinSurgeryWitness.Pcore_idempotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L426 [soft] `law-field-locker` in `structure-field KolihaDrazinSurgeryWitness.complementary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L428 [soft] `law-field-locker` in `structure-field KolihaDrazinSurgeryWitness.disjoint_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L430 [soft] `law-field-locker` in `structure-field KolihaDrazinSurgeryWitness.disjoint_right` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L434 [soft] `law-field-locker` in `structure-field KolihaDrazinSurgeryWitness.nil_agrees` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L443 [soft] `law-field-locker` in `structure-field KolihaDrazinSurgeryWitness.core_identity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L446 [soft] `law-field-locker` in `structure-field KolihaDrazinSurgeryWitness.drazin_left_core_identity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L449 [soft] `law-field-locker` in `structure-field KolihaDrazinSurgeryWitness.AD_kills_nil_right` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L451 [soft] `law-field-locker` in `structure-field KolihaDrazinSurgeryWitness.AD_kills_nil_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L453 [soft] `law-field-locker` in `structure-field KolihaDrazinSurgeryWitness.AD_supported_on_core_left` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L455 [soft] `law-field-locker` in `structure-field KolihaDrazinSurgeryWitness.AD_supported_on_core_right` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L457 [advisory] `existential-packaging` in `def KolihaDrazinSurgery` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L470 [advisory] `existential-packaging` in `def DrazinExistenceFiniteDimensional` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L470 [soft] `vacuous-prop` in `prop <vacuous>` — Prop declaration appears to reduce to True/False
  - L476 [advisory] `existential-packaging` in `def HeatKernelAsymptoticsExistence` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L482 [advisory] `existential-packaging` in `def SpectralZetaContinuationExistence` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L490 [advisory] `existential-packaging` in `def STUFreudenthalEmbeddingFor` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L490 [soft] `vacuous-prop` in `prop <vacuous>` — Prop declaration appears to reduce to True/False
  - L499 [advisory] `existential-packaging` in `def KMSExistenceSupercharge` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

