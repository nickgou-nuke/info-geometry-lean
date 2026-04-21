# Theorem Surface Index

This report is a heuristic declaration-level classification, not kernel truth.
It distinguishes likely constructive declarations from hypothesis bridges, package/reprojection surfaces, and surrogate/vacuous surfaces using the exported declaration inventory, tracked debt indices, quarantine annotations, and local source context.

## Summary
- analyzed declarations: `20128`
- theorem declarations: `11089`
- definition declarations: `9039`
- likely constructive: `10495`
- hypothesis bridges: `140`
- package / reprojection surfaces: `1053`
- surrogate / vacuous surfaces: `288`
- neutral definitions: `8152`
- declarations with audit hits: `47`
- declarations in quarantined modules: `0`

## Category Notes
- `likely_constructive`: theorem declarations with no current bridge/package/surrogate warning signal.
- `hypothesis_bridge`: theorem names or local comments explicitly advertise hypothesis-driven transport such as `_of_*_hypotheses`.
- `package_reprojection`: declarations whose module reason or local comments say they package, store, read back, or reproject witnesses/obligations.
- `surrogate_or_vacuous`: declarations hit by the live debt audits or living on surfaces marked vacuous/degenerate/identity-transport in the quarantine manifest.
- `neutral_definition`: definitions and opaque wrappers without a stronger warning signal.

## Surrogate / Vacuous Surfaces
- `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.moorePenroseRightProjector_ne_one_of_hasZeroMode` | `theorem` | `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:80` | confidence `high` | signals: audit:thinness:underscore_hypothesis:medium
- `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.moorePenroseLeftProjector_ne_one_of_hasZeroMode` | `theorem` | `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:95` | confidence `high` | signals: audit:thinness:underscore_hypothesis:medium
- `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.drazinProjection_ne_one_of_hasZeroMode` | `theorem` | `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:109` | confidence `high` | signals: audit:thinness:underscore_hypothesis:medium
- `InfoGeometry.Canonical.ClNNBottBridge.bottStep_headNullMinus` | `theorem` | `lean/InfoGeometry/Canonical/ClNNBottBridge.lean:60` | confidence `high` | signals: audit:thinness:direct_forwarder:medium
- `InfoGeometry.Canonical.ClNNBottBridge.bottStep_headNullPlus` | `theorem` | `lean/InfoGeometry/Canonical/ClNNBottBridge.lean:68` | confidence `high` | signals: audit:thinness:direct_forwarder:medium
- `InfoGeometry.Canonical.DrazinFredholmBridge.defectProjector_ne_zero_of_package` | `theorem` | `lean/InfoGeometry/Canonical/DrazinFredholmBridge.lean:175` | confidence `high` | signals: audit:thinness:underscore_hypothesis:medium; context:packaging
- `InfoGeometry.Canonical.DrazinInfiniteCore.DrazinInfiniteAssumptions.mk.inj` | `theorem` | `lean/InfoGeometry/Canonical/DrazinInfiniteCore.lean` | confidence `high` | signals: audit:surrogate:contract_decl:medium
- `InfoGeometry.Canonical.DrazinInfiniteCore.DrazinInfiniteAssumptions.mk.sizeOf_spec` | `theorem` | `lean/InfoGeometry/Canonical/DrazinInfiniteCore.lean` | confidence `high` | signals: audit:surrogate:contract_decl:medium
- `InfoGeometry.Canonical.DrazinInfiniteCore.DrazinInfiniteAssumptions.zero_isolated_spectrum` | `theorem` | `lean/InfoGeometry/Canonical/DrazinInfiniteCore.lean:531` | confidence `high` | signals: audit:surrogate:contract_decl:medium; context:hypotheses
- `InfoGeometry.Canonical.DrazinSpectralBridge.HasFiniteAscentDescentAtZero_of_zeroIsolatedInSpectrum_eq` | `theorem` | `lean/InfoGeometry/Canonical/DrazinSpectralBridge.lean:41` | confidence `high` | signals: audit:surrogate:contract_constructor:low
- `InfoGeometry.Canonical.DrazinSpectralBridge.DrazinInfiniteAssumptions_of_zeroIsolatedInSpectrum_finite_ascent_descent` | `theorem` | `lean/InfoGeometry/Canonical/DrazinSpectralBridge.lean:69` | confidence `high` | signals: audit:surrogate:contract_constructor:low; context:hypotheses; context:packaging
- `InfoGeometry.Canonical.DrazinSpectralBridge.DrazinInfiniteAssumptions_of_zeroIsolatedInSpectrum_zero_isolated` | `theorem` | `lean/InfoGeometry/Canonical/DrazinSpectralBridge.lean:82` | confidence `high` | signals: audit:surrogate:contract_constructor:low; context:hypotheses; context:packaging
- `InfoGeometry.Canonical.DrazinSpectralBridge.DrazinInfiniteAssumptions_of_zeroIsolatedInSpectrum_classical` | `theorem` | `lean/InfoGeometry/Canonical/DrazinSpectralBridge.lean:95` | confidence `high` | signals: audit:surrogate:contract_constructor:low; context:hypotheses; context:packaging
- `InfoGeometry.Canonical.DrazinSpectralBridge.DrazinInfiniteAssumptions_of_zeroIsolatedInSpectrum_generalized` | `theorem` | `lean/InfoGeometry/Canonical/DrazinSpectralBridge.lean:108` | confidence `high` | signals: audit:surrogate:contract_constructor:low; context:hypotheses; context:packaging
- `InfoGeometry.Canonical.SplitCliffordTensorBridge.splitCliffordTensorStep_headFactor` | `theorem` | `lean/InfoGeometry/Canonical/SplitCliffordTensorBridge.lean:148` | confidence `high` | signals: audit:thinness:direct_forwarder:medium
- `InfoGeometry.Canonical.SplitCliffordTensorBridge.splitCliffordTensorStep_tailFactor` | `theorem` | `lean/InfoGeometry/Canonical/SplitCliffordTensorBridge.lean:157` | confidence `high` | signals: audit:thinness:direct_forwarder:medium
- `InfoGeometry.Canonical.SplitCliffordTensorBridge.splitCliffordTensorStep_headNullMinus` | `theorem` | `lean/InfoGeometry/Canonical/SplitCliffordTensorBridge.lean:166` | confidence `high` | signals: audit:thinness:direct_forwarder:medium
- `InfoGeometry.Canonical.SplitCliffordTensorBridge.splitCliffordTensorStep_headNullPlus` | `theorem` | `lean/InfoGeometry/Canonical/SplitCliffordTensorBridge.lean:173` | confidence `high` | signals: audit:thinness:direct_forwarder:medium
- `InfoGeometry.Canonical.SplitCliffordTensorBridge.splitCl44_headFactor` | `theorem` | `lean/InfoGeometry/Canonical/SplitCliffordTensorBridge.lean:203` | confidence `high` | signals: audit:thinness:direct_forwarder:medium
- `InfoGeometry.Canonical.SplitCliffordTensorBridge.splitCl44_tailFactor` | `theorem` | `lean/InfoGeometry/Canonical/SplitCliffordTensorBridge.lean:212` | confidence `high` | signals: audit:thinness:direct_forwarder:medium

## Package / Reprojection Surfaces
- `InfoGeometry.Canonical.AQFTOperatorInterface.AQFTReadinessPackage.isCStarReadyF` | `theorem` | `lean/InfoGeometry/Canonical/AQFTReadiness.lean:26` | confidence `medium` | signals: context:packaging
- `InfoGeometry.Canonical.AQFTOperatorInterface.AQFTReadinessPackage.isCompleteCStarReadyE` | `theorem` | `lean/InfoGeometry/Canonical/AQFTReadiness.lean:27` | confidence `medium` | signals: context:packaging
- `InfoGeometry.Canonical.AQFTOperatorInterface.AQFTReadinessPackage.projectorSuperPair` | `theorem` | `lean/InfoGeometry/Canonical/AQFTReadiness.lean:29` | confidence `medium` | signals: context:packaging
- `InfoGeometry.Canonical.AnalyticalIndex.fullThermoGeoIndexCapstone_of_states` | `theorem` | `lean/InfoGeometry/Canonical/AnalyticalIndexCapstone.lean:87` | confidence `medium` | signals: context:packaging
- `InfoGeometry.Canonical.AnalyticalIndex.SinkhornRicciIndexInvariant.mk_components` | `theorem` | `lean/InfoGeometry/Canonical/AnalyticalIndexCoupled.lean:46` | confidence `medium` | signals: context:packaging
- `InfoGeometry.Canonical.BerryPhase.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace` | `theorem` | `lean/InfoGeometry/Canonical/BerryConnection.lean:30` | confidence `medium` | signals: context:packaging
- `InfoGeometry.Canonical.BogoliubovPolarizationBridge.bogoliubovPolarizationBridge_of_strictSymmetry` | `theorem` | `lean/InfoGeometry/Canonical/BogoliubovPolarizationBridge.lean:70` | confidence `medium` | signals: context:packaging
- `InfoGeometry.Canonical.BottPeriodicity.firstBottStep_consumes_doubledSpaceCl11Action_J` | `theorem` | `lean/InfoGeometry/Canonical/BottPeriodicity.lean:162` | confidence `medium` | signals: context:packaging
- `InfoGeometry.Canonical.BottPeriodicity.firstBottStep_consumes_doubledSpaceCl11Action_K` | `theorem` | `lean/InfoGeometry/Canonical/BottPeriodicity.lean:175` | confidence `medium` | signals: context:packaging
- `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.NontrivialRegularizationPackage.hMP` | `theorem` | `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:50` | confidence `medium` | signals: context:packaging
- `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.NontrivialRegularizationPackage.hD` | `theorem` | `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:51` | confidence `medium` | signals: context:packaging
- `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.NontrivialRegularizationPackage.drazinProjection_ne_one` | `theorem` | `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:56` | confidence `medium` | signals: context:packaging
- `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.ZeroModeRegularizationPackage.v_zeroMode` | `theorem` | `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:67` | confidence `medium` | signals: context:packaging
- `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.ZeroModeRegularizationPackage.v_ne_zero` | `theorem` | `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:68` | confidence `medium` | signals: context:packaging
- `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.exists_nontrivial_regularization_pair_of_dim_mismatch` | `theorem` | `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:125` | confidence `medium` | signals: context:packaging
- `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.exists_zeroMode_and_nontrivial_regularization_pair_of_dim_mismatch` | `theorem` | `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:219` | confidence `medium` | signals: context:packaging
- `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge.exists_nontrivial_regularization_pair_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel` | `theorem` | `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:305` | confidence `medium` | signals: context:packaging
- `InfoGeometry.Canonical.CanonicalGaugeBridge.firstVariation_referenceInvariant` | `theorem` | `lean/InfoGeometry/Canonical/CanonicalGaugeBridge.lean:101` | confidence `medium` | signals: context:packaging
- `InfoGeometry.Canonical.CapstoneSemanticAudit.similarity_preserves_idempotent_and_commute` | `theorem` | `lean/InfoGeometry/Canonical/CapstoneSemanticAudit.lean:87` | confidence `medium` | signals: context:packaging
- `InfoGeometry.Canonical.CasimirWeylDrazinContext.CasimirWeylDrazinData.regularCoreHamiltonian_support_flow_package` | `theorem` | `lean/InfoGeometry/Canonical/CasimirWeylDrazinContext.lean:156` | confidence `medium` | signals: context:packaging

## Hypothesis Bridges
- `InfoGeometry.Canonical.ConformalUnification.ConformalInference.dilationSource_eq_neg_half_projectorObstruction_of_structuredProjectorHypotheses` | `theorem` | `lean/InfoGeometry/Canonical/ConformalAnomalyOperator.lean:123` | confidence `high` | signals: context:hypotheses; name:hypotheses
- `InfoGeometry.Canonical.WeylKKTAnomalyIdentity.ConformalInference.dilationCommutator_eq_neg_half_projectorObstruction_of_structuredProjectorHypotheses` | `theorem` | `lean/InfoGeometry/Canonical/WeylKKTAnomalyIdentity.lean:95` | confidence `high` | signals: context:hypotheses; name:hypotheses
- `InfoGeometry.Canonical.AnalyticalIndex.chiralSliceIsoAlong_of_noZeroEigenCrossing_path` | `theorem` | `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:498` | confidence `medium` | signals: context:hypotheses
- `InfoGeometry.Canonical.AnalyticalIndex.indexInvariantAlong_of_modularCliffordTransport_components` | `theorem` | `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:868` | confidence `medium` | signals: context:hypotheses
- `InfoGeometry.Canonical.ArnoldNetworkIntertwiner.arnoldToDoubledKrein_readoutPreservation_of_pointwise_eq` | `theorem` | `lean/InfoGeometry/Canonical/ArnoldNetworkIntertwiner.lean:59` | confidence `medium` | signals: context:hypotheses
- `InfoGeometry.Canonical.BogoliubovTransport.modularVariance_nonneg_iff_signed_secondMoment_nonneg` | `theorem` | `lean/InfoGeometry/Canonical/BogoliubovTransport.lean:1437` | confidence `medium` | signals: context:hypotheses
- `InfoGeometry.Canonical.BogoliubovWeightedKMSCertification.lorentzBivectorSeed_operatorialKMS_of_structural` | `theorem` | `lean/InfoGeometry/Canonical/BogoliubovWeightedKMSCertification.lean:133` | confidence `medium` | signals: context:hypotheses
- `InfoGeometry.Canonical.BogoliubovWeightedKMSCertification.weightedNonequilibrium_sinkhornKMSClosure_of_structural` | `theorem` | `lean/InfoGeometry/Canonical/BogoliubovWeightedKMSCertification.lean:220` | confidence `medium` | signals: context:hypotheses
- `InfoGeometry.Canonical.BoundaryChiralIndexBridge.transportedHasZeroMode_of_operatorialCentralCharge_ne_zero_of_identifiedTransportedPolarization` | `theorem` | `lean/InfoGeometry/Canonical/BoundaryChiralIndexBridge.lean:108` | confidence `medium` | signals: context:hypotheses; context:packaging
- `InfoGeometry.Canonical.CalabiYauBridge.absDet_cramerRaoMetric_eq_one_of_rnEntropySource_of_unitRelativeVolume` | `theorem` | `lean/InfoGeometry/Canonical/CalabiYauRNMongeAmpere.lean:60` | confidence `medium` | signals: context:hypotheses
- `InfoGeometry.Canonical.CalabiYauBridge.logAbsDet_cramerRaoMetric_eq_zero_of_rnEntropySource_of_unitRelativeVolume` | `theorem` | `lean/InfoGeometry/Canonical/CalabiYauRNMongeAmpere.lean:82` | confidence `medium` | signals: context:hypotheses
- `InfoGeometry.Canonical.ConformalAlgebra.ConformalBeliefAlgebra.generatorCartanDecomposition_of_parts` | `theorem` | `lean/InfoGeometry/Canonical/ConformalAlgebra.lean:110` | confidence `medium` | signals: context:hypotheses
- `InfoGeometry.Canonical.ConformalUnification.ConformalInference.obstructionOperatorOwner_of_kkt_wings` | `theorem` | `lean/InfoGeometry/Canonical/ConformalAnomalyOperator.lean:53` | confidence `medium` | signals: context:hypotheses
- `InfoGeometry.Canonical.ConformalUnification.ConformalInference.projectorObstruction_isGZero_of_kkt_wings` | `theorem` | `lean/InfoGeometry/Canonical/ConformalAnomalySource.lean:34` | confidence `medium` | signals: context:hypotheses
- `InfoGeometry.Canonical.ConformalUnification.ConformalInference.squashedProjectorObstruction_isGZero_of_kkt_wings` | `theorem` | `lean/InfoGeometry/Canonical/ConformalAnomalySource.lean:427` | confidence `medium` | signals: context:hypotheses
- `InfoGeometry.Canonical.ConformalUnification.ConformalInference.chiralAnomaly_eq_zero_of_kahlerLogDet_normalized_fixedpoint` | `theorem` | `lean/InfoGeometry/Canonical/ConformalAnomalySource.lean:645` | confidence `medium` | signals: context:hypotheses
- `InfoGeometry.Canonical.ConformalUnification.ConformalCanopyPackage.hA` | `theorem` | `lean/InfoGeometry/Canonical/ConformalUnification.lean:26` | confidence `medium` | signals: context:hypotheses; context:packaging
- `InfoGeometry.Canonical.ConnesArakiFramework.topologicalBekensteinBound_and_tomitaModularKMS_of_tomitaConnesArakiData` | `theorem` | `lean/InfoGeometry/Canonical/ConnesArakiTomita.lean:91` | confidence `medium` | signals: context:hypotheses
- `InfoGeometry.Canonical.ConnesArakiFramework.topologicalBekensteinBound_and_tomitaModularKMS_of_tomitaConnesArakiData_root` | `theorem` | `lean/InfoGeometry/Canonical/ConnesArakiTomita.lean:120` | confidence `medium` | signals: context:hypotheses
- `InfoGeometry.Canonical.DiracSouriau.hasDrazinInverse_of_kktChiralContext` | `theorem` | `lean/InfoGeometry/Canonical/DiracSouriauKKTChiralContext.lean:39` | confidence `medium` | signals: context:hypotheses

## Likely Constructive Declarations
- `InfoGeometry.Algebraic.Fitting.ascent_le` | `theorem` | `lean/InfoGeometry/Algebraic/Fitting.lean:27` | confidence `low` | signals: -
- `InfoGeometry.Algebraic.Fitting.descent_le` | `theorem` | `lean/InfoGeometry/Algebraic/Fitting.lean:47` | confidence `low` | signals: -
- `InfoGeometry.Algebraic.Fitting.ker_pow_eq_of_ascent_stabilized` | `theorem` | `lean/InfoGeometry/Algebraic/Fitting.lean:70` | confidence `low` | signals: -
- `InfoGeometry.Algebraic.Fitting.range_pow_eq_of_descent_stabilized` | `theorem` | `lean/InfoGeometry/Algebraic/Fitting.lean:79` | confidence `low` | signals: -
- `InfoGeometry.Algebraic.Fitting.isCompl_ker_pow_range_pow` | `theorem` | `lean/InfoGeometry/Algebraic/Fitting.lean:88` | confidence `low` | signals: -
- `InfoGeometry.Algebraic.Fitting.surjective_on_range` | `theorem` | `lean/InfoGeometry/Algebraic/Fitting.lean:122` | confidence `low` | signals: -
- `InfoGeometry.Algebraic.Fitting.injective_on_range` | `theorem` | `lean/InfoGeometry/Algebraic/Fitting.lean:133` | confidence `low` | signals: -
- `InfoGeometry.Architecture.SpinFactor.spinFactor_poly_identity` | `theorem` | `lean/InfoGeometry/Architecture/SpinFactor.lean:27` | confidence `low` | signals: -
- `InfoGeometry.Architecture.SpinFactor.spinFactorPotential_well_defined` | `theorem` | `lean/InfoGeometry/Architecture/SpinFactor.lean:47` | confidence `low` | signals: -
- `InfoGeometry.Architecture.SpinFactor.spinFactorPotential_zero` | `theorem` | `lean/InfoGeometry/Architecture/SpinFactor.lean:54` | confidence `low` | signals: -
- `InfoGeometry.Architecture.CartanInvolution.fixedSubgroup.eq_1` | `theorem` | `lean/InfoGeometry/Architecture/SymmetricSpace.lean` | confidence `low` | signals: -
- `InfoGeometry.Architecture.CartanInvolution.mk.inj` | `theorem` | `lean/InfoGeometry/Architecture/SymmetricSpace.lean` | confidence `low` | signals: -
- `InfoGeometry.Architecture.CartanInvolution.mk.sizeOf_spec` | `theorem` | `lean/InfoGeometry/Architecture/SymmetricSpace.lean` | confidence `low` | signals: -
- `InfoGeometry.Architecture.CartanInvolution.ofMulAutInvolution.congr_simp` | `theorem` | `lean/InfoGeometry/Architecture/SymmetricSpace.lean` | confidence `low` | signals: -
- `InfoGeometry.Architecture.SymmetricPair.mk.inj` | `theorem` | `lean/InfoGeometry/Architecture/SymmetricSpace.lean` | confidence `low` | signals: -
- `InfoGeometry.Architecture.SymmetricPair.mk.sizeOf_spec` | `theorem` | `lean/InfoGeometry/Architecture/SymmetricSpace.lean` | confidence `low` | signals: -
- `InfoGeometry.Architecture.SymmetricSpace.mk.inj` | `theorem` | `lean/InfoGeometry/Architecture/SymmetricSpace.lean` | confidence `low` | signals: -
- `InfoGeometry.Architecture.SymmetricSpace.mk.sizeOf_spec` | `theorem` | `lean/InfoGeometry/Architecture/SymmetricSpace.lean` | confidence `low` | signals: -
- `InfoGeometry.Architecture.cartanSymmetryOfInvolutiveMulAut.eq_1` | `theorem` | `lean/InfoGeometry/Architecture/SymmetricSpace.lean` | confidence `low` | signals: -
- `InfoGeometry.Architecture.SymmetricSpace.symm_involutive` | `theorem` | `lean/InfoGeometry/Architecture/SymmetricSpace.lean:16` | confidence `low` | signals: -

## Modules With Highest Non-Constructive Load
| Module | Hypothesis bridges | Package surfaces | Surrogate/vacuous | Total |
| :--- | ---: | ---: | ---: | ---: |
| `InfoGeometry.Core.SymmetricLie` | 2 | 8 | 41 | 51 |
| `InfoGeometry.Meta.ProofShape` | 0 | 15 | 20 | 35 |
| `InfoGeometry.Canonical.SingularBoundaryCorrection` | 0 | 32 | 0 | 32 |
| `InfoGeometry.Canonical.ModularSuperchargeClosure` | 8 | 21 | 2 | 31 |
| `InfoGeometry.Canonical.UnifiedSuperchargeAlgebra` | 0 | 31 | 0 | 31 |
| `InfoGeometry.Canonical.DrazinInfiniteCore` | 1 | 17 | 12 | 30 |
| `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge` | 0 | 26 | 3 | 29 |
| `InfoGeometry.Canonical.TypeIIIContinuousCoreReal` | 0 | 12 | 14 | 26 |
| `InfoGeometry.Canonical.SpectralInference` | 1 | 24 | 0 | 25 |
| `InfoGeometry.Canonical.ConformalProjectorCore` | 0 | 24 | 0 | 24 |
| `InfoGeometry.Meta.Admission` | 0 | 0 | 23 | 23 |
| `InfoGeometry.Meta.RegionPolicy` | 0 | 0 | 21 | 21 |
| `InfoGeometry.Canonical.PhaseSpaceWeylCausalBridge` | 5 | 16 | 0 | 21 |
| `InfoGeometry.Canonical.GenerativeInferenceCore` | 0 | 19 | 0 | 19 |
| `InfoGeometry.Quantum.RealMajoranaCategory` | 0 | 18 | 0 | 18 |
| `InfoGeometry.Canonical.HeadTrialityCore` | 0 | 17 | 0 | 17 |
| `InfoGeometry.Canonical.OperatorPenroseUnification` | 0 | 16 | 0 | 16 |
| `InfoGeometry.Canonical.Unification` | 2 | 14 | 0 | 16 |
| `InfoGeometry.Canonical.LogDetRadonNikodymMechanism` | 0 | 15 | 0 | 15 |
| `InfoGeometry.Canonical.RealBdGDIIIAtom` | 0 | 15 | 0 | 15 |

## Quarantine Anchors
- `InfoGeometry.Canonical.AQFTOperatorInterface` | downgraded to a preparation layer, but still only packages readiness certificates beside compression/interpretation surrogates
- `InfoGeometry.Canonical.AnomalyDilationBridge` | bridge theorem layer depends on quarantined conformal synthesis and cannot yet live on the stable surface
- `InfoGeometry.Canonical.BeliefDynamics` | finite scaffold hardcodes identity transport and metric replacement semantics
- `InfoGeometry.Canonical.BerryPhase` | canonical bridge remains on the vacuity quarantine surface
- `InfoGeometry.Canonical.CalabiYauBridge` | closure state stores the Ricci-flat/constant-density witness it later reprojects
- `InfoGeometry.Canonical.ChiralAction` | canonical bridge remains on the vacuity quarantine surface
- `InfoGeometry.Canonical.ChiralCliffordBridge` | torsion/chiral bridge packages caller-supplied witnesses into theorem-shaped interfaces
- `InfoGeometry.Canonical.ChiralTorsionBridge` | theorem surface projects stored torsion/chiral witnesses instead of deriving them
- `InfoGeometry.Canonical.ChiralTorsionRelativeVolume` | imports quarantined BeliefDynamics and still sits on the review-surface facade path
- `InfoGeometry.Canonical.ConformalWard` | Ward identity is baked into the definition of the variation
- `InfoGeometry.Canonical.ConnesArakiFramework` | theorem surface is a packaged readback over stored Casini/bridge witnesses rather than independent derivation
- `InfoGeometry.Canonical.CountEmergentFlow` | imports quarantined HolographicEmergence and still sits on the review-surface facade path
- `InfoGeometry.Canonical.CountSubstrateBridge` | count-first bridge re-exports the quarantined holographic package
- `InfoGeometry.Canonical.DeepHorizon` | facade re-exports quarantined holographic-emergence claims
- `InfoGeometry.Canonical.DiracRicciBridge` | bridge uses constant/zero trajectory surrogates in its canonical API
- `InfoGeometry.Canonical.GrandSynthesis` | capstone package depends on quarantined vacuous bridge modules
- `InfoGeometry.Canonical.GrandUnificationBlueprint` | grand-unification identity is promoted from tautological anomaly cancellation
- `InfoGeometry.Canonical.HolographicEmergence` | vacuum-apex twistor closure is driven by a zero quadratic form surrogate
- `InfoGeometry.Canonical.InformationCalculus` | continuum interface is built on the scalar/identity Yang-Mills scaffold
- `InfoGeometry.Canonical.MasterSynthesis` | synthesis theorem repackages supplied witnesses and degenerate path choices

## Interpretation
- This index is intentionally conservative: a declaration is only marked suspicious when the live audits, the quarantine manifest, the declaration name, or the local source context say so.
- A declaration in `likely_constructive` is not proved to be deep; it simply lacks the current signals of packaging or vacuity.
- Use this report together with the quarantine manifest and debt indices to decide what deserves promotion or demolition.

