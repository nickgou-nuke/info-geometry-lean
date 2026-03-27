# Theory Audit Report

Generated: 2026-03-27 02:25:56Z

## Build toolchain status
- lake: available (/home/goutev/.elan/bin/lake)
```bash
Lake version 5.0.0-src+7e01a1b (Lean version 4.28.0)
```

## Placeholder proof debt (sorry/admit)

```text
```

- Total placeholder occurrences in canonical tree: 0

## Axiom declarations

```text
```
- Total explicit axiom declarations: 0

## Namespace audit

```text
[audit] Project namespace: InfoGeometry
[audit] Scanning root:       ./lean/InfoGeometry

[audit] Files with namespace InfoGeometry*: 401
[audit] Files missing namespace InfoGeometry*: 71

=== Missing namespace InfoGeometry ===
./lean/InfoGeometry/All.lean
./lean/InfoGeometry/Architecture/All.lean
./lean/InfoGeometry/Canonical/AQFTOperatorInterface.lean
./lean/InfoGeometry/Canonical/Algebra.lean
./lean/InfoGeometry/Canonical/All.lean
./lean/InfoGeometry/Canonical/AnalyticalIndex.lean
./lean/InfoGeometry/Canonical/BerryPhase.lean
./lean/InfoGeometry/Canonical/CalabiYauBridge.lean
./lean/InfoGeometry/Canonical/ChiralTorsionBridge.lean
./lean/InfoGeometry/Canonical/Clifford.lean
./lean/InfoGeometry/Canonical/ConformalUnification.lean
./lean/InfoGeometry/Canonical/ConnesArakiFramework.lean
./lean/InfoGeometry/Canonical/CountSinkhornFlow.lean
./lean/InfoGeometry/Canonical/CountSubstrateBridge.lean
./lean/InfoGeometry/Canonical/DrazinAdjoint.lean
./lean/InfoGeometry/Canonical/Foundations.lean
./lean/InfoGeometry/Canonical/Geometry.lean
./lean/InfoGeometry/Canonical/GrandCanonicalCore.lean
./lean/InfoGeometry/Canonical/KK.lean
./lean/InfoGeometry/Canonical/KKFoundation.lean
./lean/InfoGeometry/Canonical/KMSSinkhornBridge.lean
./lean/InfoGeometry/Canonical/Krein.lean
./lean/InfoGeometry/Canonical/KreinNaturalFlow.lean
./lean/InfoGeometry/Canonical/MoorePenroseAdjoint.lean
./lean/InfoGeometry/Canonical/OperatorAlgebraBridge.lean
./lean/InfoGeometry/Canonical/PerelmanW.lean
./lean/InfoGeometry/Canonical/Prequantum.lean
./lean/InfoGeometry/Canonical/Projective.lean
./lean/InfoGeometry/Canonical/Quantum.lean
./lean/InfoGeometry/Canonical/Statistics.lean
./lean/InfoGeometry/Canonical/Thermo.lean
./lean/InfoGeometry/Canonical/Twistor.lean
./lean/InfoGeometry/Canonical/WeylInformationGauge.lean
./lean/InfoGeometry/Canonical/YangMillsFinite.lean
./lean/InfoGeometry/Cartan.lean
./lean/InfoGeometry/Causal/All.lean
./lean/InfoGeometry/Clifford/All.lean
./lean/InfoGeometry/Clifford/Supercharge.lean
./lean/InfoGeometry/Convex.lean
./lean/InfoGeometry/Convex/All.lean
./lean/InfoGeometry/Core.lean
./lean/InfoGeometry/Core/All.lean
./lean/InfoGeometry/Core/Derivatives.lean
./lean/InfoGeometry/ExponentialFamily.lean
./lean/InfoGeometry/ExponentialFamily/All.lean
./lean/InfoGeometry/Generated.lean
./lean/InfoGeometry/Jordan/All.lean
./lean/InfoGeometry/KK/All.lean
./lean/InfoGeometry/Krein/All.lean
./lean/InfoGeometry/Krein/Dilation.lean
./lean/InfoGeometry/Krein/Grading.lean
./lean/InfoGeometry/LLM.lean
./lean/InfoGeometry/Library.lean
./lean/InfoGeometry/MaxEnt.lean
./lean/InfoGeometry/MaxEnt/All.lean
./lean/InfoGeometry/MaxEnt/JaynesInfoStatMechTest.lean
./lean/InfoGeometry/Measure/All.lean
./lean/InfoGeometry/MeasureProjective/All.lean
./lean/InfoGeometry/OptimalTransport.lean
./lean/InfoGeometry/Potential.lean
./lean/InfoGeometry/Prequantum/All.lean
./lean/InfoGeometry/Projective/All.lean
./lean/InfoGeometry/Quantum/All.lean
./lean/InfoGeometry/Singular.lean
./lean/InfoGeometry/Singular/All.lean
./lean/InfoGeometry/SuperUnified.lean
./lean/InfoGeometry/Thermo/All.lean
./lean/InfoGeometry/Unstable/Quarantine.lean
./lean/InfoGeometry/Volume/All.lean
./lean/InfoGeometry/auto_blueprints.lean
./lean/InfoGeometry/generalizedKL.lean

=== Files declaring a non-InfoGeometry namespace (heuristic) ===

=== Namespace prefix histogram (first namespace line per file) ===
    415 InfoGeometry
      5 SymmetricLieAlgebra
      4 PositiveMeasure
      3 ProjectivePrequantumBundle
      3 Projective
      3 IsMoorePenroseInverse
      3 IsDrazinInverse
      3 ConformalInference
      2 YangMillsMassGapBridge
      2 WeylGaugeField
      2 TransformerBlock
      2 RealSplitKreinKasparovCycle
      2 RealMajoranaDatum
      2 PrequantumData
      2 PolarizedMajorana
      2 ModularRadonNikodymData
      2 MaskedTransformerBlock
      2 LogPotential
      2 LogGenerator
      2 KreinSpace
      2 KreinGradedModule
      2 KPolarization
      2 ExactAbelianizingBridge
      1 alphaConnection
      1 WeylTrajectory
      1 WeylLineIntegrator
      1 WeylDifferentialOperator
      1 TwistedGaussianFamily
      1 TopologicalMajoranaShadow
      1 ThermalModel

[audit] Done.
```

## Orphaned Lean file audit

```text
[orphaned-check] Empty directory found:
lean/tmp
lean/InfoGeometry/Exploration/Legacy
```

## Quarantine Boundary Audit

```text
Forbidden quarantined import: InfoGeometry.Canonical.AQFTOperatorInterface in lean/InfoGeometry/Canonical/All.lean:24
Forbidden quarantined import: InfoGeometry.Canonical.AnomalyDilationBridge in lean/InfoGeometry/Canonical/All.lean:25
Forbidden quarantined import: InfoGeometry.Canonical.BeliefDynamics in lean/InfoGeometry/Canonical/ChiralTorsionRelativeVolume.lean:1
Forbidden quarantined import: InfoGeometry.Canonical.BerryPhase in lean/InfoGeometry/Canonical/All.lean:35
Forbidden quarantined import: InfoGeometry.Canonical.ChiralAction in lean/InfoGeometry/Canonical/All.lean:48
Forbidden quarantined import: InfoGeometry.Canonical.ChiralCliffordBridge in lean/InfoGeometry/Canonical/ConformalAlgebra.lean:2
Forbidden quarantined import: InfoGeometry.Canonical.ConformalWard in lean/InfoGeometry/Canonical/All.lean:55
Forbidden quarantined import: InfoGeometry.Canonical.ConnesArakiFramework in lean/InfoGeometry/Canonical/All.lean:56
Forbidden quarantined import: InfoGeometry.Canonical.CountSubstrateBridge in lean/InfoGeometry/Canonical/All.lean:57
Forbidden quarantined import: InfoGeometry.Canonical.DeepHorizon in lean/InfoGeometry/Canonical/All.lean:59
Forbidden quarantined import: InfoGeometry.Canonical.GrandSynthesis in lean/InfoGeometry/Canonical/All.lean:93
Forbidden quarantined import: InfoGeometry.Canonical.GrandSynthesis in lean/InfoGeometry/Canonical/All.lean:97
Forbidden quarantined import: InfoGeometry.Canonical.GrandUnificationBlueprint in lean/InfoGeometry/Canonical/All.lean:95
Forbidden quarantined import: InfoGeometry.Canonical.HolographicEmergence in lean/InfoGeometry/Canonical/CountEmergentFlow.lean:2
Forbidden quarantined import: InfoGeometry.Canonical.InformationCalculus in lean/InfoGeometry/Canonical/All.lean:100
Forbidden quarantined import: InfoGeometry.Canonical.InformationCalculus in lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean:2
Forbidden quarantined import: InfoGeometry.Canonical.InformationCalculus in lean/InfoGeometry/Canonical/KreinDiracSpectralLift.lean:1
Forbidden quarantined import: InfoGeometry.Canonical.MasterSynthesis in lean/InfoGeometry/Canonical/All.lean:125
Forbidden quarantined import: InfoGeometry.Canonical.OperatorAlgebraBridge in lean/InfoGeometry/Canonical/All.lean:130
Forbidden quarantined import: InfoGeometry.Canonical.RedLine in lean/InfoGeometry/Canonical/All.lean:151
Forbidden quarantined import: InfoGeometry.Canonical.RedLine in lean/InfoGeometry/Canonical/LogSpineBridge.lean:2
Forbidden quarantined import: InfoGeometry.Canonical.Rosetta in lean/InfoGeometry/Canonical/All.lean:137
Forbidden quarantined import: InfoGeometry.Canonical.YangMillsFinite in lean/InfoGeometry/Canonical/All.lean:168
Forbidden quarantined import: InfoGeometry.Prequantum.Connection in lean/InfoGeometry/Prequantum/All.lean:1
Forbidden quarantined import: InfoGeometry.Prequantum.Quotient in lean/InfoGeometry/Prequantum/All.lean:2
Forbidden quarantined import: InfoGeometry.Projective.TwistorBridge in lean/InfoGeometry/Projective/All.lean:17
Forbidden quarantined import: InfoGeometry.Projective.TwistorBridge in lean/InfoGeometry/Canonical/All.lean:171
Quarantine import boundary check failed.
```

## Exact Constructivity Audit

```text
Constructivity audit (full tree)
No exact constructivity violations found.
```

## Review-Only Surrogate Audit

```text
Constructivity audit (review-only full tree)
review-projection-theorem: lean/InfoGeometry/Canonical/BogoliubovPolarizationBridge.lean:39: transportK_sq_of_strictSymmetryBogoliubov reduces to `exact h.toBogoliubovTransform_transportP_eq`
review-projection-theorem: lean/InfoGeometry/Canonical/CalabiYauMetricRicci.lean:124: metricLogDet_eq_zero_of_unitRelativeVolume reduces to `exact abs_pos.mpr`
review-projection-theorem: lean/InfoGeometry/Canonical/CayleyBregmanBridge.lean:121: grad_transport_back reduces to `simpa [Bridge.toTransport, Bridge.toBounded, Bridge.toUnbounded] using h.symm`
review-projection-theorem: lean/InfoGeometry/Canonical/CayleyBregmanBridge.lean:162: quadraticPotential_deriv reduces to `simpa [nabla, toHessianGeometry] using hspec.trans`
review-projection-theorem: lean/InfoGeometry/Canonical/ChiralAction.lean:49: chiralDirac_eq_of_unitRelativeVolume reduces to `exact CI.isNormalInference_of_kahlerLogDet_unitRelativeVolume`
review-projection-theorem: lean/InfoGeometry/Canonical/ChiralEinsteinBridge.lean:109: anomalyDriven_fixedpoint_tracks_source reduces to `simpa using hEq.symm`
review-projection-theorem: lean/InfoGeometry/Canonical/ConformalAlgebra.lean:79: scale_anomaly_emergence reduces to `simpa [SatisfiesFlatWeights, SatisfiesPWeight, SatisfiesKWeight] using CBA.anomaly_breaks_weights`
review-projection-theorem: lean/InfoGeometry/Canonical/ConformalAlgebra.lean:137: M_in_volumePreserving_of_cartan reduces to `exact hCartan.1`
review-projection-theorem: lean/InfoGeometry/Canonical/ConformalAlgebra.lean:143: D_in_weylDilation_of_cartan reduces to `exact hCartan.2`
review-projection-theorem: lean/InfoGeometry/Canonical/ConformalAlgebra.lean:367: scale_anomaly_obstructs_weyl_flatness reduces to `exact CBA.scale_anomaly_breaks_weight_closure`
review-projection-theorem: lean/InfoGeometry/Canonical/ConformalAnomalySource.lean:149: projectors_commute_of_kahlerLogDet_unitRelativeVolume reduces to `exact CI.projectors_commute_of_chiralScale_eq_zero`
review-projection-theorem: lean/InfoGeometry/Canonical/ConformalProjectorCore.lean:62: spectralProjector_idempotent reduces to `simpa [CertifiedConformalInference.spectralProjector] using
    CCI.toCertifiedInverseKernel.spectralProjector_idempotent`
review-projection-theorem: lean/InfoGeometry/Canonical/ConformalProjectorCore.lean:68: mpRangeProjector_idempotent reduces to `simpa [CertifiedConformalInference.mpRangeProjector] using
    CCI.toCertifiedInverseKernel.mpRangeProjector_idempotent`
review-projection-theorem: lean/InfoGeometry/Canonical/ConformalProjectorCore.lean:74: metricProjector_idempotent reduces to `simpa [CertifiedConformalInference.metricProjector] using
    CCI.toCertifiedInverseKernel.metricProjector_idempotent`
review-projection-theorem: lean/InfoGeometry/Canonical/ConformalProjectorCore.lean:80: metricProjector_star reduces to `simpa [CertifiedConformalInference.metricProjector] using
    CCI.toCertifiedInverseKernel.metricProjector_star`
review-projection-theorem: lean/InfoGeometry/Canonical/ConformalProjectorCore.lean:86: mpRangeProjector_star reduces to `simpa [CertifiedConformalInference.mpRangeProjector] using
    CCI.toCertifiedInverseKernel.mpRangeProjector_star`
review-projection-theorem: lean/InfoGeometry/Canonical/ConformalProjectorCore.lean:112: specialConformal_eq_modularInversion_translation reduces to `simpa using hJPJ.symm`
review-projection-theorem: lean/InfoGeometry/Canonical/IBTopological.lean:26: F_deriv_eq_neg_gibbsExpectation reduces to `simpa [F, Gibbs, IBGibbsMeasure, mul_comm, mul_left_comm, mul_assoc] using h.symm`
review-constant-function: lean/InfoGeometry/Canonical/MultiplicativeToAdditiveBridge.lean:69: defect is a constant function returning 1
review-projection-theorem: lean/InfoGeometry/Canonical/QFTTDFTLaunchpad.lean:51: rungeGrossStationaryDualState_of_stationaryAtScale reduces to `exact hStationary.2`
review-projection-theorem: lean/InfoGeometry/Canonical/Singular.lean:244: exists_drazinInverse_global reduces to `simpa [B] using hDlin.2.1`
review-constant-function: lean/InfoGeometry/Canonical/SinkhornFoundation.lean:127: leftScale is a constant function returning 1
review-constant-function: lean/InfoGeometry/Canonical/SinkhornFoundation.lean:128: rightScale is a constant function returning 1
review-projection-theorem: lean/InfoGeometry/Canonical/SpectralInference.lean:313: dirac_sq_eq_metric reduces to `exact IST.compatibility.inner_dirac_sq`
review-projection-theorem: lean/InfoGeometry/Canonical/WeylPathHysteresis.lean:171: twistedInference_updateOrderPathDependent reduces to `exact T.has_torsion`
review-projection-theorem: lean/InfoGeometry/Clifford/Grading.lean:158: spectral_epsilon_isOdd reduces to `simpa [creationLike, annihilationLike, ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply] using h.symm`
review-projection-theorem: lean/InfoGeometry/Clifford/Grading.lean:176: spectral_decomposition reduces to `simpa [ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply] using h.symm`
review-projection-theorem: lean/InfoGeometry/Convex/Duality.lean:27: KL_param_eq_bregman_swap reduces to `exact hconv.deriv_le_slope`
review-projection-theorem: lean/InfoGeometry/Convex/HessianGeometry.lean:125: divergence_nonneg reduces to `simpa [divergence, dualMap] using H.divergence_nonneg_axiom`
review-projection-theorem: lean/InfoGeometry/Convex/HessianGeometry.lean:145: metricOp_isSymmetric reduces to `simpa [HessianGeometry.metricOp] using hx.hasFDerivAt`
review-projection-theorem: lean/InfoGeometry/Convex/HessianGeometry.lean:213: metric_nonneg reduces to `simpa [HessianGeometry.metric, real_inner_comm] using H.metric_quadratic_nonneg`
review-projection-theorem: lean/InfoGeometry/Core/SymmetricLie.lean:388: minusPart_smul reduces to `simpa [plusPartLinear] using hs.linear_image`
review-projection-theorem: lean/InfoGeometry/Core/SymmetricLie.lean:409: convex_minusPart_image reduces to `simpa [minusPartLinear] using hs.linear_image`
review-projection-theorem: lean/InfoGeometry/Core/SymmetricLie.lean:414: convex_plusPart_preimage reduces to `simpa [plusPartLinear] using hs.linear_preimage`
review-projection-theorem: lean/InfoGeometry/Core/SymmetricLie.lean:419: convex_minusPart_preimage reduces to `simpa [minusPartLinear] using hs.linear_preimage`
review-projection-theorem: lean/InfoGeometry/Core/SymmetricLieGeneric.lean:257: killing_invariant reduces to `simpa using h1.symm`
review-projection-theorem: lean/InfoGeometry/ExponentialFamily/TwistedGaussian.lean:44: adjoint_infoOperator reduces to `simpa [infoOperator] using TG.normal_commutes`
review-projection-theorem: lean/InfoGeometry/Jordan/SPD.lean:21: SPD reduces to `simpa [Matrix.IsSymm] using A.symm`
review-projection-theorem: lean/InfoGeometry/KK/KasparovCycle.lean:79: comm_compact_lie reduces to `simpa [Ring.lie_def] using X.comm_compact`
review-projection-theorem: lean/InfoGeometry/KK/RealSplitKreinCompactOperator.lean:22: superComm_eps_isCompactOperator reduces to `simpa [IsCompactEnd] using X.superComm_eps_compact`
review-projection-theorem: lean/InfoGeometry/KK/RealSplitKreinCompactOperator.lean:28: superComm_J_isCompactOperator reduces to `simpa [IsCompactEnd] using X.superComm_J_compact`
review-projection-theorem: lean/InfoGeometry/KK/RealSplitKreinCompactOperator.lean:34: superComm_pi_isCompactOperator reduces to `simpa [IsCompactEnd] using X.superComm_pi_compact`
review-projection-theorem: lean/InfoGeometry/KK/RealSplitKreinCompactOperator.lean:40: comm_isCompactOperator reduces to `simpa [IsCompactEnd] using X.comm_compact`
review-projection-theorem: lean/InfoGeometry/KK/RealSplitKreinResolvent.lean:59: isCompactOperator reduces to `simpa [IsCompactEnd] using R.compact`
review-projection-theorem: lean/InfoGeometry/Krein/KreinSpace.lean:210: isKreinSkewAdjoint_iff reduces to `exact add_eq_zero_iff_eq_neg.mp`
review-identity-function: lean/InfoGeometry/LLM/PositionalEncoding.lean:15: encode is an identity function
review-projection-theorem: lean/InfoGeometry/MaxEnt/Core.lean:137: IsMaxEntSolution reduces to `exact hP.2`
review-projection-theorem: lean/InfoGeometry/MaxEnt/Finite.lean:263: sum_toReal_eq_one reduces to `simpa [tsum_fintype] using P.tsum_coe`
review-projection-theorem: lean/InfoGeometry/MaxEnt/Finite.lean:368: satisfiesTargetMoments_iff reduces to `exact J.gibbsMoment_eq_sum`
review-constant-function: lean/InfoGeometry/MaxEnt/Finite.lean:545: target is a constant function returning 0
review-projection-theorem: lean/InfoGeometry/MaxEnt/Jaynes.lean:100: partitionWithPrior_pos reduces to `simpa [tsum_fintype] using q.tsum_coe`
review-projection-theorem: lean/InfoGeometry/MaxEnt/Lagrange.lean:30: maxEnt_stationary reduces to `simpa using hextr.exists_multipliers_of_hasStrictFDerivAt`
review-projection-theorem: lean/InfoGeometry/Measure/DiscreteRN.lean:63: rnDeriv_pmf_eq_div reduces to `simpa using Q.toMeasure_apply_singleton`
review-projection-theorem: lean/InfoGeometry/Projective/GaugeReduction.lean:58: generalizedKL_eq_klLike_of_Z_eq reduces to `exact sub_eq_zero.mpr`
review-projection-theorem: lean/InfoGeometry/Quantum/BulkBoundary.lean:545: hNegPhaseDimMismatch_of_boundaryLocalizationBridge reduces to `exact hLoc.boundaryLocalized_to_dimMismatch`
review-identity-linear-map: lean/InfoGeometry/Quantum/KitaevChain.lean:42: U is a constant LinearMap.id map
review-projection-theorem: lean/InfoGeometry/Quantum/KitaevChain.lean:221: zero_exists_of_opposite_sign reduces to `exact Set.mem_uIcc.mpr`
review-projection-theorem: lean/InfoGeometry/Quantum/KitaevChain.lean:253: index_change_forces_defect_crossing reduces to `exact sign_eq_neg_one_iff.mp`
review-identity-function: lean/InfoGeometry/Quantum/RealKCategory.lean:207: invFun is an identity function
review-projection-theorem: lean/InfoGeometry/Quantum/RealMajorana.lean:71: car_realization_of_clifford reduces to `simpa [pairing] using M.car`
review-projection-theorem: lean/InfoGeometry/Quantum/RealMajorana.lean:137: mem_weylMinus_iff reduces to `simpa using M.Pi_sq.symm`
review-projection-theorem: lean/InfoGeometry/Quantum/RealMajorana.lean:513: transportGamma_car reduces to `simpa [transportGamma] using M.car`
review-projection-theorem: lean/InfoGeometry/Quantum/RealMajorana.lean:524: car_realization_of_clifford reduces to `exact T.transportGamma_car`
review-projection-theorem: lean/InfoGeometry/Quantum/RealMajorana.lean:1121: Hom reduces to `simpa [Hom.toBogoliubovTransform, RealBogoliubovTransform.preservesPolarization] using
    h.intertwines_polarization`
review-projection-theorem: lean/InfoGeometry/Quantum/SplitCliffordAtom.lean:63: Hom reduces to `simpa [jOp] using f.homCore.comm_J`
review-projection-theorem: lean/InfoGeometry/Quantum/SplitCliffordAtom.lean:67: Hom reduces to `simpa [epsOp] using f.homCore.comm_eps`
review-projection-theorem: lean/InfoGeometry/Quantum/SplitCliffordAtom.lean:71: Hom reduces to `simpa [kOp] using f.homCore.comm_K`
review-projection-theorem: lean/InfoGeometry/Thermo/FiniteMatrix.lean:43: partitionFunction_ne_zero reduces to `simpa [partitionFunction, gibbsWeight, logUnnormalizedDensity] using M.partition_ne_zero`
review-constant-function: lean/InfoGeometry/Volume/ConnesCocycle.lean:245: defect is a constant function returning 1
```

## Notes
- This report is static when lake is unavailable; full proof checking requires successful lake build.
