# Theory Audit Report

Generated: 2026-03-21 13:06:39Z

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

[audit] Files with namespace InfoGeometry*: 326
[audit] Files missing namespace InfoGeometry*: 50

=== Missing namespace InfoGeometry ===
./lean/InfoGeometry/All.lean
./lean/InfoGeometry/Canonical/Algebra.lean
./lean/InfoGeometry/Canonical/All.lean
./lean/InfoGeometry/Canonical/Clifford.lean
./lean/InfoGeometry/Canonical/DrazinAdjoint.lean
./lean/InfoGeometry/Canonical/Foundations.lean
./lean/InfoGeometry/Canonical/GeneralizedKL.lean
./lean/InfoGeometry/Canonical/Geometry.lean
./lean/InfoGeometry/Canonical/GrandCanonicalCore.lean
./lean/InfoGeometry/Canonical/KK.lean
./lean/InfoGeometry/Canonical/KKFoundation.lean
./lean/InfoGeometry/Canonical/Krein.lean
./lean/InfoGeometry/Canonical/KreinNaturalFlow.lean
./lean/InfoGeometry/Canonical/MoorePenroseAdjoint.lean
./lean/InfoGeometry/Canonical/Prequantum.lean
./lean/InfoGeometry/Canonical/Projective.lean
./lean/InfoGeometry/Canonical/Quantum.lean
./lean/InfoGeometry/Canonical/RobustThermodynamicRegression.lean
./lean/InfoGeometry/Canonical/Statistics.lean
./lean/InfoGeometry/Canonical/Thermo.lean
./lean/InfoGeometry/Canonical/Twistor.lean
./lean/InfoGeometry/Cartan.lean
./lean/InfoGeometry/Clifford/Lift.lean
./lean/InfoGeometry/Clifford/Supercharge.lean
./lean/InfoGeometry/Convex.lean
./lean/InfoGeometry/Core.lean
./lean/InfoGeometry/Core/Derivatives.lean
./lean/InfoGeometry/Cramer.lean
./lean/InfoGeometry/ExponentialFamily.lean
./lean/InfoGeometry/Generated.lean
./lean/InfoGeometry/Krein/All.lean
./lean/InfoGeometry/Krein/Category.lean
./lean/InfoGeometry/Krein/Dilation.lean
./lean/InfoGeometry/Krein/Grading.lean
./lean/InfoGeometry/Krein/KreinSpace.lean
./lean/InfoGeometry/Krein/Prelude.lean
./lean/InfoGeometry/Krein/State.lean
./lean/InfoGeometry/Krein/Superalgebra.lean
./lean/InfoGeometry/Krein/TestTimeout.lean
./lean/InfoGeometry/LLM.lean
./lean/InfoGeometry/Library.lean
./lean/InfoGeometry/MaxEnt.lean
./lean/InfoGeometry/MaxEnt/JaynesInfoStatMechTest.lean
./lean/InfoGeometry/OptimalTransport.lean
./lean/InfoGeometry/Potential.lean
./lean/InfoGeometry/Singular.lean
./lean/InfoGeometry/SuperUnified.lean
./lean/InfoGeometry/Unstable/Quarantine.lean
./lean/InfoGeometry/auto_blueprints.lean
./lean/InfoGeometry/generalizedKL.lean

=== Files declaring a non-InfoGeometry namespace (heuristic) ===
./lean/InfoGeometry/Canonical/RobustThermodynamicRegression.lean :: 26:namespace FUSION
./lean/InfoGeometry/Krein/Category.lean :: 25:namespace Krein
./lean/InfoGeometry/Krein/KreinSpace.lean :: 54:namespace KreinSpace
./lean/InfoGeometry/Krein/State.lean :: 26:namespace KreinStateSpace
./lean/InfoGeometry/Krein/Superalgebra.lean :: 7:namespace KreinGradedModule

=== Namespace prefix histogram (first namespace line per file) ===
    334 InfoGeometry
      6 PositiveMeasure
      5 SymmetricLieAlgebra
      3 ProjectivePrequantumBundle
      3 IsMoorePenroseInverse
      3 IsDrazinInverse
      2 YangMillsMassGapBridge
      2 WeylGaugeField
      2 TransformerBlock
      2 RealMajoranaDatum
      2 ModularRadonNikodymData
      2 MaskedTransformerBlock
      2 LogPotential
      2 LogGenerator
      2 KreinSpace
      2 KreinGradedModule
      2 KPolarization
      2 ExactAbelianizingBridge
      2 ConformalInference
      1 alphaConnection
      1 WeylTrajectory
      1 WeylLineIntegrator
      1 WeylDifferentialOperator
      1 TwistedGaussianFamily
      1 TopologicalMajoranaShadow
      1 ThermalModel
      1 ThermalDiagonal
      1 SymmetricCliffordModule
      1 SuperWeightLike
      1 StrongRicciFromHessian

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
Forbidden quarantined import: InfoGeometry.Canonical.ConformalUnification in lean/InfoGeometry/Canonical/WeylTransportChiralBridge.lean:2
Forbidden quarantined import: InfoGeometry.Canonical.Rosetta in lean/InfoGeometry/Quantum/RosettaSynthesis.lean:1
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
review-projection-theorem: lean/InfoGeometry/Canonical/CayleyBregmanBridge.lean:123: grad_transport_back reduces to `simpa [Bridge.toTransport, Bridge.toBounded, Bridge.toUnbounded] using h.symm`
review-projection-theorem: lean/InfoGeometry/Canonical/CayleyBregmanBridge.lean:162: quadraticPotential_deriv reduces to `simpa [nabla, toHessianGeometry] using hspec.trans`
review-projection-theorem: lean/InfoGeometry/Canonical/ChiralEinsteinBridge.lean:113: anomalyDriven_fixedpoint_tracks_source reduces to `simpa using hEq.symm`
review-projection-theorem: lean/InfoGeometry/Canonical/ConformalAlgebra.lean:88: scale_anomaly_emergence reduces to `simpa [SatisfiesFlatWeights, SatisfiesPWeight, SatisfiesKWeight] using CBA.anomaly_breaks_weights`
review-projection-theorem: lean/InfoGeometry/Canonical/ConformalAlgebra.lean:143: M_in_volumePreserving_of_cartan reduces to `exact hCartan.1`
review-projection-theorem: lean/InfoGeometry/Canonical/ConformalAlgebra.lean:149: D_in_weylDilation_of_cartan reduces to `exact hCartan.2`
review-projection-theorem: lean/InfoGeometry/Canonical/ConformalAlgebra.lean:373: scale_anomaly_obstructs_weyl_flatness reduces to `exact CBA.scale_anomaly_breaks_weight_closure`
review-projection-theorem: lean/InfoGeometry/Canonical/ConformalUnification.lean:69: spectralProjector_idempotent reduces to `simpa [CertifiedConformalInference.spectralProjector] using
    CCI.toCertifiedInverseKernel.spectralProjector_idempotent`
review-projection-theorem: lean/InfoGeometry/Canonical/ConformalUnification.lean:75: mpRangeProjector_idempotent reduces to `simpa [CertifiedConformalInference.mpRangeProjector] using
    CCI.toCertifiedInverseKernel.mpRangeProjector_idempotent`
review-projection-theorem: lean/InfoGeometry/Canonical/ConformalUnification.lean:81: metricProjector_idempotent reduces to `simpa [CertifiedConformalInference.metricProjector] using
    CCI.toCertifiedInverseKernel.metricProjector_idempotent`
review-projection-theorem: lean/InfoGeometry/Canonical/ConformalUnification.lean:87: metricProjector_star reduces to `simpa [CertifiedConformalInference.metricProjector] using
    CCI.toCertifiedInverseKernel.metricProjector_star`
review-projection-theorem: lean/InfoGeometry/Canonical/ConformalUnification.lean:93: mpRangeProjector_star reduces to `simpa [CertifiedConformalInference.mpRangeProjector] using
    CCI.toCertifiedInverseKernel.mpRangeProjector_star`
review-projection-theorem: lean/InfoGeometry/Canonical/ConformalUnification.lean:122: specialConformal_eq_modularInversion_translation reduces to `simpa using hJPJ.symm`
review-projection-theorem: lean/InfoGeometry/Canonical/ConformalUnification.lean:455: projectors_commute_of_kahlerLogDet_unitRelativeVolume reduces to `exact CI.projectors_commute_of_chiralScale_eq_zero`
review-projection-theorem: lean/InfoGeometry/Canonical/IBTopological.lean:26: F_deriv_eq_neg_gibbsExpectation reduces to `simpa [F, Gibbs, IBGibbsMeasure, mul_comm, mul_left_comm, mul_assoc] using h.symm`
review-constant-function: lean/InfoGeometry/Canonical/MultiplicativeToAdditiveBridge.lean:69: defect is a constant function returning 1
review-projection-theorem: lean/InfoGeometry/Canonical/QFTTDFTLaunchpad.lean:260: rungeGrossStationaryDualState_of_stationaryAtScale reduces to `exact hStationary.2`
review-projection-theorem: lean/InfoGeometry/Canonical/Singular.lean:252: exists_drazinInverse_global reduces to `simpa [B] using hDlin.2.1`
review-projection-theorem: lean/InfoGeometry/Canonical/WeylInformationGauge.lean:182: twistedInference_updateOrderPathDependent reduces to `exact T.has_torsion`
review-projection-theorem: lean/InfoGeometry/Canonical/WeylInformationGauge.lean:278: cartanWeyl_generator_split reduces to `exact CBA.cartan_generator_split`
review-projection-theorem: lean/InfoGeometry/Clifford/Grading.lean:160: spectral_epsilon_isOdd reduces to `simpa [creationLike, annihilationLike, ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply] using h.symm`
review-projection-theorem: lean/InfoGeometry/Clifford/Grading.lean:176: spectral_decomposition reduces to `simpa [ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply] using h.symm`
review-projection-theorem: lean/InfoGeometry/Convex/Duality.lean:27: KL_param_eq_bregman_swap reduces to `exact hconv.deriv_le_slope`
review-projection-theorem: lean/InfoGeometry/Convex/HessianGeometry.lean:127: divergence_nonneg reduces to `simpa [divergence, dualMap] using H.divergence_nonneg_axiom`
review-projection-theorem: lean/InfoGeometry/Core/SymmetricLie.lean:388: minusPart_smul reduces to `simpa [plusPartLinear] using hs.linear_image`
review-projection-theorem: lean/InfoGeometry/Core/SymmetricLie.lean:409: convex_minusPart_image reduces to `simpa [minusPartLinear] using hs.linear_image`
review-projection-theorem: lean/InfoGeometry/Core/SymmetricLie.lean:414: convex_plusPart_preimage reduces to `simpa [plusPartLinear] using hs.linear_preimage`
review-projection-theorem: lean/InfoGeometry/Core/SymmetricLie.lean:419: convex_minusPart_preimage reduces to `simpa [minusPartLinear] using hs.linear_preimage`
review-projection-theorem: lean/InfoGeometry/Core/SymmetricLieGeneric.lean:257: killing_invariant reduces to `simpa using h1.symm`
review-projection-theorem: lean/InfoGeometry/ExponentialFamily/TwistedGaussian.lean:49: adjoint_infoOperator reduces to `simpa [infoOperator] using TG.normal_commutes`
review-projection-theorem: lean/InfoGeometry/Jordan/SPD.lean:21: SPD reduces to `simpa [Matrix.IsSymm] using A.symm`
review-projection-theorem: lean/InfoGeometry/KK/KasparovCycle.lean:64: comm_compact_lie reduces to `simpa [Ring.lie_def] using X.comm_compact`
review-projection-theorem: lean/InfoGeometry/Krein/KreinSpace.lean:213: isKreinSkewAdjoint_iff reduces to `exact add_eq_zero_iff_eq_neg.mp`
review-identity-function: lean/InfoGeometry/LLM/PositionalEncoding.lean:15: encode is an identity function
review-projection-theorem: lean/InfoGeometry/MaxEnt/Core.lean:139: IsMaxEntSolution reduces to `exact hP.2`
review-projection-theorem: lean/InfoGeometry/MaxEnt/Finite.lean:265: sum_toReal_eq_one reduces to `simpa [tsum_fintype] using P.tsum_coe`
review-projection-theorem: lean/InfoGeometry/MaxEnt/Finite.lean:370: satisfiesTargetMoments_iff reduces to `exact J.gibbsMoment_eq_sum`
review-constant-function: lean/InfoGeometry/MaxEnt/Finite.lean:545: target is a constant function returning 0
review-projection-theorem: lean/InfoGeometry/MaxEnt/Jaynes.lean:102: partitionWithPrior_pos reduces to `simpa [tsum_fintype] using q.tsum_coe`
review-projection-theorem: lean/InfoGeometry/MaxEnt/Lagrange.lean:33: maxEnt_stationary reduces to `simpa using hextr.exists_multipliers_of_hasStrictFDerivAt`
review-projection-theorem: lean/InfoGeometry/Measure/DiscreteRN.lean:67: rnDeriv_pmf_eq_div reduces to `simpa using Q.toMeasure_apply_singleton`
review-projection-theorem: lean/InfoGeometry/Projective/GaugeReduction.lean:56: generalizedKL_eq_klLike_of_Z_eq reduces to `exact sub_eq_zero.mpr`
review-projection-theorem: lean/InfoGeometry/Quantum/BulkBoundary.lean:549: hNegPhaseDimMismatch_of_boundaryLocalizationBridge reduces to `exact hLoc.boundaryLocalized_to_dimMismatch`
review-identity-linear-map: lean/InfoGeometry/Quantum/KitaevChain.lean:40: U is a constant LinearMap.id map
review-projection-theorem: lean/InfoGeometry/Quantum/KitaevChain.lean:223: zero_exists_of_opposite_sign reduces to `exact Set.mem_uIcc.mpr`
review-projection-theorem: lean/InfoGeometry/Quantum/KitaevChain.lean:256: index_change_forces_defect_crossing reduces to `exact sign_eq_neg_one_iff.mp`
review-identity-function: lean/InfoGeometry/Quantum/RealKCategory.lean:207: invFun is an identity function
review-projection-theorem: lean/InfoGeometry/Quantum/RealMajorana.lean:76: car_realization_of_clifford reduces to `simpa [pairing] using M.car`
review-projection-theorem: lean/InfoGeometry/Quantum/RealMajorana.lean:137: mem_weylMinus_iff reduces to `simpa using M.Pi_sq.symm`
review-projection-theorem: lean/InfoGeometry/Quantum/RealMajorana.lean:515: transportGamma_car reduces to `simpa [transportGamma] using M.car`
review-projection-theorem: lean/InfoGeometry/Quantum/RealMajorana.lean:530: car_realization_of_clifford reduces to `exact T.transportGamma_car`
review-projection-theorem: lean/InfoGeometry/Quantum/SplitCliffordAtom.lean:63: Hom reduces to `simpa [jOp] using f.homCore.comm_J`
review-projection-theorem: lean/InfoGeometry/Quantum/SplitCliffordAtom.lean:67: Hom reduces to `simpa [epsOp] using f.homCore.comm_eps`
review-projection-theorem: lean/InfoGeometry/Quantum/SplitCliffordAtom.lean:71: Hom reduces to `simpa [kOp] using f.homCore.comm_K`
review-projection-theorem: lean/InfoGeometry/Thermo/FiniteMatrix.lean:43: partitionFunction_ne_zero reduces to `simpa [partitionFunction, gibbsWeight, logUnnormalizedDensity] using M.partition_ne_zero`
review-constant-function: lean/InfoGeometry/Volume/ConnesCocycle.lean:245: defect is a constant function returning 1
```

## Notes
- This report is static when lake is unavailable; full proof checking requires successful lake build.
