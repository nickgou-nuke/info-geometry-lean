# Equivalence Dictionary

Maintained dictionary of equivalent naming surfaces extracted from Lean source. It combines theorem/lemma `=` and `↔` relations with `def`/`abbrev` alias surfaces.

## Summary
- `lean_file_count`: `792`
- `declaration_count`: `6379`
- `auto_relation_count`: `2073`
- `curated_relation_count`: `13`
- `relation_count`: `2086`
- `resolved_pair_count`: `605`
- `unresolved_head_token_total_raw`: `1966`
- `unresolved_head_unique_count_raw`: `557`
- `unresolved_head_token_total`: `242`
- `unresolved_head_unique_count`: `84`
- `unresolved_ambiguous_token_total`: `242`
- `unresolved_ambiguous_unique_count`: `84`
- `unresolved_missing_token_total`: `1724`
- `unresolved_missing_unique_count`: `473`
- `unresolved_missing_nonlocal_token_total`: `987`
- `unresolved_missing_nonlocal_unique_count`: `419`
- `component_count`: `162`
- `parse_failure_count`: `0`
- `curated_registry`: `docs/NameEquivalenceRegistry.json`
- `curated_enabled`: `True`

## Update Command
```bash
python3 tools/infra/generate_equivalence_dictionary.py --curated-json docs/NameEquivalenceRegistry.json --json-out reports/dag/equivalence-dictionary.json --md-out reports/dag/equivalence-dictionary.md
```

## Largest Equivalence Components
- `EQC-0021` size `31` edges `40` relationKinds `{'iff': 9, 'alias': 4, 'eq': 40}`
  members: `CCI.leftChiralAnomalyOperator`, `CCI.liftedEinsteinAnomalyOperator`, `CCI.liftedLeftChiralAnomalyOperator`, `CCI.liftedProjectorObstructionOperator`, `CCI.liftedRightChiralAnomalyOperator`, `CCI.rightChiralAnomalyOperator`, `CI.P_D`, `CI.P_MP_right`, `CI.actionStructureConstantOp`, `CI.chiralAnomaly`, `CI.chiralAnomalyOperator`, `CI.chiralScale`
  sample declarations:
  - `InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.liftedLeftChiralAnomalyOperator_eq_zero_iff`
  - `InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.liftedLeftChiralAnomalyOperator_ne_zero_iff`
  - `InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.projectorObstructionOperator`
  - `InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.liftedEinsteinAnomalyOperator_eq_neg_liftedLeftChiralAnomalyOperator_of_projectorAgreement`
  - `InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.liftedEinsteinAnomalyOperator_eq_neg_liftedProjectorObstructionOperator_of_projectorAgreement`
- `EQC-0037` size `28` edges `30` relationKinds `{'eq': 37}`
  members: `ContinuousLinearMap.id`, `J.comp`, `LinearMap.id`, `M.K.comp`, `M.sigma`, `P0.involution.comp`, `S.P_plus`, `S.P_plus.comp`, `S.Pplus`, `S.Pplus.comp`, `T.informationalDiracSquare`, `T.polarization.Pminus.comp`
  sample declarations:
  - `InfoGeometry.Krein.K_sq_of_relations`
  - `InfoGeometry.Quantum.RealMajorana.RealMajoranaDatum.K_sq`
  - `InfoGeometry.Quantum.ModularAnomaly.TopologicalMajoranaShadow.sigma_zero_clm`
  - `InfoGeometry.Quantum.RealMajorana.RealBogoliubovTransform.transportK_sq`
  - `InfoGeometry.Quantum.RealMajorana.RealBogoliubovTransform.transportPi_sq`
- `EQC-0026` size `22` edges `36` relationKinds `{'iff': 6, 'eq': 43}`
  members: `CIK.A`, `CIK.GammaG`, `CIK.GammaS`, `CIK.IsEP`, `CIK.SpectralMetricCommute`, `CIK.SpectralRangeCommute`, `CIK.chiralAnomaly`, `CIK.chiralScale`, `CIK.dilationGap`, `CIK.metricProjector`, `CIK.mpRangeProjector`, `CIK.projectorMismatch`
  sample declarations:
  - `InfoGeometry.Canonical.CertifiedInverseKernel.isEP_iff_comm`
  - `InfoGeometry.Canonical.CertifiedInverseKernel.GammaG_eq_two_smul_dilationGap`
  - `InfoGeometry.Canonical.SingularDecompositionSurrogate.spectral_dilation_anomaly_relations`
  - `InfoGeometry.Canonical.CertifiedInverseKernel.GammaS_mul_spectralComplementaryProjector`
  - `InfoGeometry.Canonical.CertifiedInverseKernel.GammaS_eq_two_mul_spectralProjector_sub_one`
- `EQC-0047` size `13` edges `16` relationKinds `{'iff': 6, 'eq': 11}`
  members: `IK.A`, `IK.IsEP`, `IK.SpectralMetricCommute`, `IK.SpectralRangeCommute`, `IK.chiralAnomaly`, `IK.chiralScale`, `IK.dilationGap`, `IK.metricProjector`, `IK.mpRangeProjector`, `IK.projectorMismatch`, `IK.rightChiralAnomaly`, `IK.rightProjectorMismatch`
  sample declarations:
  - `InfoGeometry.Canonical.InverseKernel.isEP_iff_comm`
  - `InfoGeometry.Canonical.InverseKernel.isEP_iff_dilationGap_eq_zero`
  - `InfoGeometry.Canonical.InverseKernel.chiralAnomaly_eq_zero_iff_spectralMetricCommute`
  - `InfoGeometry.Canonical.InverseKernel.rightChiralAnomaly_eq_zero_iff_spectralRangeCommute`
  - `InfoGeometry.Canonical.InverseKernel.chiralScale_eq_zero_iff_chiralAnomaly_eq_zero`
- `EQC-0089` size `11` edges `10` relationKinds `{'curated_alias': 10}`
  members: `InfoGeometry.Canonical.OperatorDictionary.phaseAxisK`, `InfoGeometry.Canonical.ProjectorEquivariance.HestenesI`, `InfoGeometry.Canonical.QuantumLieAlgebroidRosetta.internalPhaseAxis`, `InfoGeometry.Canonical.RealBdG.modularK`, `InfoGeometry.Canonical.TomitaTakesaki.clockAxis`, `InfoGeometry.Canonical.TomitaTakesaki.modularComplexI`, `InfoGeometry.Canonical.TomitaTakesaki.phaseAxisK`, `InfoGeometry.Canonical.WindingOrbitClosure.clockAxis`, `InfoGeometry.Krein.clockAxis`, `InfoGeometry.Krein.complex_i`, `InfoGeometry.Krein.dilationOperator`
  sample declarations:
  - `curated::6`
  - `curated::9`
  - `curated::7`
  - `curated::8`
  - `curated::3`
- `EQC-0061` size `9` edges `9` relationKinds `{'eq': 5, 'alias': 5}`
  members: `InfoGeometry.Canonical.CertifiedModularReduction.Kambient`, `InfoGeometry.Canonical.CertifiedModularReduction.Kphys`, `InfoGeometry.Canonical.CertifiedModularReduction.Pmetric`, `InfoGeometry.Canonical.CertifiedModularReduction.Preg`, `InfoGeometry.Canonical.CertifiedModularReduction.Pzero`, `InfoGeometry.Canonical.compress`, `InfoGeometry.Canonical.metricProjectorOf`, `c.cik.spectralComplementaryProjector`, `c.cik.spectralProjector`
  sample declarations:
  - `InfoGeometry.Canonical.CertifiedModularReduction.Kambient_supported_on_Preg`
  - `InfoGeometry.Canonical.CertifiedModularReduction.Kambient_kills_Pzero`
  - `InfoGeometry.Canonical.CertifiedModularReduction.Kambient`
  - `InfoGeometry.Canonical.CertifiedModularReduction.Kphys_supported_on_metric`
  - `InfoGeometry.Canonical.CertifiedModularReduction.Kphys_kills_Pzero_of_alignment`
- `EQC-0016` size `9` edges `8` relationKinds `{'eq': 13, 'alias': 1}`
  members: `C.kernel.rightChiralAnomaly`, `CIK.toInformationCartanTriple.GammaS`, `DrazinSupercharge.CertifiedInverseKernel.superHamiltonian`, `DrazinSupercharge.CertifiedInverseKernel.supercharge`, `DrazinSupercharge.commutator`, `InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.supercharge`, `InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.superchargeK`, `InfoGeometry.Canonical.DrazinSupercharge.commutator`, `InfoGeometry.Canonical.DrazinSupercharge.commutatorK`
  sample declarations:
  - `InfoGeometry.Canonical.ClosureDrazinBridge.ConstructiveClosureDrazinData.commutator_P_D_GammaG_eq_sub_anomalies`
  - `InfoGeometry.Canonical.ClosureDrazinBridge.ConstructiveClosureDrazinData.commutator_P_D_dilationGap_eq_half_sub_anomalies`
  - `InfoGeometry.Canonical.SingularDecompositionSurrogate.superHamiltonian_even_relation`
  - `InfoGeometry.Canonical.SingularDecompositionSurrogate.supercharge_odd_relation`
  - `InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.supercharge_mul_GammaS_eq_neg`
- `EQC-0019` size `8` edges `7` relationKinds `{'eq': 8}`
  members: `CCI.bogoliubovConjugate_liftedEinsteinAnomalyOperator`, `CCI.bogoliubovConjugate_liftedLeftChiralAnomalyOperator`, `CCI.bogoliubovConjugate_liftedRightChiralAnomalyOperator`, `CIK.spectralGradingFlow`, `NormedSpace.exp`, `Real.cos`, `Real.cosh`, `T.spectralGradingFlow`
  sample declarations:
  - `InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.bogoliubovConjugate_liftedEinsteinAnomalyOperator_eq_exp_mul_mul_exp_neg`
  - `InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.bogoliubovConjugate_liftedLeftChiralAnomalyOperator_eq_exp_mul_mul_exp_neg`
  - `InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.bogoliubovConjugate_liftedRightChiralAnomalyOperator_eq_exp_mul_mul_exp_neg`
  - `InfoGeometry.Canonical.CertifiedInverseKernel.spectralGradingFlow_eq_cosh_add_sinh_GammaS`
  - `InfoGeometry.Canonical.BogoliubovClosedForms.exp_eq_cos_add_sin_of_sq_eq_neg_one`
- `EQC-0057` size `7` edges `8` relationKinds `{'alias': 2, 'eq': 6}`
  members: `InfoGeometry.Canonical.CartanDecomposition.InformationCartanTriple.IsSpectralCompact`, `InfoGeometry.Canonical.CartanDecomposition.InformationCartanTriple.IsSpectralNonCompact`, `T.GammaS`, `T.spectralAdjointFlow`, `T.spectralComplement`, `T.spectralProjector`, `T.thetaS`
  sample declarations:
  - `InfoGeometry.Canonical.CartanDecomposition.InformationCartanTriple.IsSpectralCompact`
  - `InfoGeometry.Canonical.CartanDecomposition.InformationCartanTriple.IsSpectralNonCompact`
  - `InfoGeometry.Canonical.CartanDecomposition.InformationCartanTriple.GammaS_mul_spectralComplement`
  - `InfoGeometry.Canonical.CartanDecomposition.InformationCartanTriple.GammaS_mul_spectralProjector`
  - `InfoGeometry.Canonical.CartanDecomposition.InformationCartanTriple.spectralComplement_fixed_under_spectralGradingFlow`
- `EQC-0008` size `7` edges `6` relationKinds `{'eq': 6}`
  members: `B.covariantDerivative`, `B.covariantSectionAlong`, `B.curvatureAlong`, `B.fieldStrength`, `B.respond`, `B.transform`, `B.transformByPotential`
  sample declarations:
  - `InfoGeometry.Canonical.covariantDerivative_transformSection_eq`
  - `InfoGeometry.Canonical.WeylGaugeField.covariantSectionAlong_transform_eq`
  - `InfoGeometry.Canonical.WeylGaugeField.curvatureAlong_transformByPotential_eq`
  - `InfoGeometry.Canonical.fieldStrength_transformByPotential_eq`
  - `InfoGeometry.Canonical.WeylGaugeField.respond_transform_eq_of_isGaugeInvariant`
- `EQC-0091` size `7` edges `6` relationKinds `{'eq': 10}`
  members: `InfoGeometry.Canonical.PositiveRayCore.logDensity`, `J.energy`, `R.rn.modularHamiltonian`, `Real.log`, `ambientRelativeBridge.projectiveLogDensity`, `recompositionData.minusLogDefect`, `recompositionData.plusLogDefect`
  sample declarations:
  - `InfoGeometry.Canonical.PhaseSpaceRecompositionExample.sourceRay_logDensity_zero`
  - `InfoGeometry.Canonical.PhaseSpaceRecompositionExample.sourceRay_logDensity_one`
  - `InfoGeometry.Canonical.PhaseSpaceRecompositionExample.targetRay_logDensity_zero`
  - `InfoGeometry.Canonical.PhaseSpaceRecompositionExample.targetRay_logDensity_one`
  - `InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.log_gibbsRatio_eq_energy_sub_logPartition`
- `EQC-0122` size `6` edges `7` relationKinds `{'eq': 6, 'iff': 1}`
  members: `InfoGeometry.Projective.projectiveMap`, `InfoGeometry.Projective.projectiveMapEven`, `InfoGeometry.Projective.projectivize`, `InfoGeometry.Projective.same_ray`, `InfoGeometry.Projective.vacuum`, `IsKreinIsometry.id`
  sample declarations:
  - `InfoGeometry.Projective.projectiveMap_mk`
  - `InfoGeometry.Projective.projectiveMap_vacuum`
  - `InfoGeometry.Projective.projectiveMap_id`
  - `InfoGeometry.Projective.projectiveMapEven_mk`
  - `InfoGeometry.Projective.projectiveMapEven_vacuum`
- `EQC-0099` size `6` edges `6` relationKinds `{'iff': 4, 'eq': 5}`
  members: `InfoGeometry.Canonical.SpinorModularBridge.coriolisVorticity`, `S.boundaryGenerator`, `S.boundaryScale`, `S.leftProjector`, `S.rightBoundaryGenerator`, `S.spectralProjector`
  sample declarations:
  - `InfoGeometry.Canonical.BoundaryLocalizationIndexEquiv.boundaryScale_ne_zero_iff_coriolisVorticity_ne_zero`
  - `InfoGeometry.Canonical.BoundaryLocalizationIndexEquiv.boundaryScale_ne_zero_iff_boundaryGenerator_ne_zero`
  - `InfoGeometry.Canonical.SingularBoundaryCorrection.boundaryScale_eq_zero_iff_boundaryGenerator_eq_zero`
  - `InfoGeometry.Canonical.SingularBoundaryCorrection.boundaryGenerator_eq_projector_commutator`
  - `InfoGeometry.Canonical.SingularBoundaryCorrection.boundaryGenerator_eq_zero_iff_projectors_commute`
- `EQC-0041` size `6` edges `5` relationKinds `{'alias': 5}`
  members: `Equiv.Perm`, `InfoGeometry.Canonical.MoE.ModeDiracMassProfile`, `InfoGeometry.Canonical.MoE.ModeMass`, `InfoGeometry.Canonical.MoE.ModewiseSplitRep`, `InfoGeometry.Canonical.MoE.PermMode`, `InfoGeometry.Canonical.MoE.PermutationMode`
  sample declarations:
  - `InfoGeometry.Canonical.MoE.PermMode`
  - `InfoGeometry.Canonical.MoE.ModeDiracMassProfile`
  - `InfoGeometry.Canonical.MoE.ModeMass`
  - `InfoGeometry.Canonical.MoE.ModewiseSplitRep`
  - `InfoGeometry.Canonical.MoE.PermutationMode`
- `EQC-0045` size `6` edges `5` relationKinds `{'eq': 5}`
  members: `H.gibbsWeight`, `InfoGeometry.ExponentialFamily.Class.multinomialDensity`, `InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.gibbsWeight`, `M.modularOperator`, `Real.exp`, `bernoulliHessianGeometry.metric`
  sample declarations:
  - `InfoGeometry.Thermal.FiniteMatrix.Hamiltonian.gibbsWeight_eq_exp_logDensity`
  - `InfoGeometry.ExponentialFamily.Class.multinomial_density_eq`
  - `InfoGeometry.Thermo.FiniteDiagonal.gibbsWeight_eq_exp_logDensity`
  - `InfoGeometry.Canonical.OperatorialInformationLift.modularOperator_eq_exp_neg_scalarModularPotential_smul_id`
  - `InfoGeometry.ExponentialFamily.Bernoulli.bernoulli_metric`
- `EQC-0048` size `6` edges `5` relationKinds `{'alias': 5}`
  members: `Id.run`, `InfoGeometry.Lint.lintDecl`, `InfoGeometry.Meta.directlyUsedConstants`, `InfoGeometry.Meta.evaluateAdmission`, `InfoGeometry.Meta.taggedDependencyViolations`, `InfoGeometry.Meta.transitivelyUsedConstants`
  sample declarations:
  - `InfoGeometry.Lint.lintDecl`
  - `InfoGeometry.Meta.directlyUsedConstants`
  - `InfoGeometry.Meta.evaluateAdmission`
  - `InfoGeometry.Meta.taggedDependencyViolations`
  - `InfoGeometry.Meta.transitivelyUsedConstants`
- `EQC-0076` size `6` edges `5` relationKinds `{'eq': 5}`
  members: `InfoGeometry.Canonical.FierzReadout.FierzChannelReadout.toQuantumPresentationWith`, `R.hilbert`, `R.scalar`, `R.symplectic`, `R.toQuantumPresentation.metricReadout`, `R.toQuantumPresentation.phaseReadout`
  sample declarations:
  - `InfoGeometry.Canonical.FierzReadout.FierzChannelReadout.toQuantumPresentationWith_metricReadout`
  - `InfoGeometry.Canonical.FierzReadout.FierzChannelReadout.toQuantumPresentationWith_phaseReadout`
  - `InfoGeometry.Canonical.FierzReadout.FierzChannelReadout.fierz_majorana`
  - `InfoGeometry.Canonical.FierzReadout.FierzChannelReadout.toQuantumPresentation_metricReadout`
  - `InfoGeometry.Canonical.FierzReadout.FierzChannelReadout.toQuantumPresentation_phaseReadout`
- `EQC-0012` size `5` edges `4` relationKinds `{'eq': 5}`
  members: `BogoliubovTransport.modularTransportGenerator`, `DrazinSupercharge.CertifiedInverseKernel.superHamiltonianK`, `M.T.adjointFlow`, `M.T.generator`, `Real.pi`
  sample declarations:
  - `InfoGeometry.Canonical.ComplexMaskTransmutationBridge.superHamiltonian_eq_modularTransportGenerator_lorentzBivectorSeed_transmuted`
  - `InfoGeometry.Canonical.ModularSuperchargeClosure.CanonicalSeedTomitaCompatibility.superHamiltonian_fixed_under_tomitaAdjointFlow`
  - `InfoGeometry.Canonical.ModularSuperchargeClosure.CanonicalSeedTomitaCompatibility.superHamiltonian_eq_tomitaGenerator`
  - `InfoGeometry.Canonical.ModularSuperchargeClosure.superHamiltonian_eq_two_pi_smul_canonicalInternalModularHamiltonian`
  - `InfoGeometry.Canonical.ModularSuperchargeClosure.CanonicalSeedUnruhCompatibility.superHamiltonian_eq_two_pi_modularHamiltonian`
- `EQC-0022` size `5` edges `4` relationKinds `{'alias': 1, 'eq': 3}`
  members: `CI.A`, `InfoGeometry.Canonical.ConformalUnification.ConformalInference.P`, `J.gibbsDist`, `J.gibbsProb`, `J.prior`
  sample declarations:
  - `InfoGeometry.Canonical.ConformalUnification.ConformalInference.P`
  - `InfoGeometry.MaxEnt.IProjection.gibbs_is_unique_minimizer`
  - `InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.gibbsDist_pointwise`
  - `InfoGeometry.MaxEnt.Finite.FiniteJaynesProblem.gibbsProb_eq_prior_mul_exp_tilt`
- `EQC-0024` size `5` edges `4` relationKinds `{'eq': 2, 'alias': 2}`
  members: `CI.D`, `InfoGeometry.Canonical.ConformalUnification.ConformalInference.P_MP`, `InfoGeometry.Canonical.ConformalUnification.ConformalInference.P_MP_right`, `IsMoorePenroseInverse.leftProjector`, `IsMoorePenroseInverse.rightProjector`
  sample declarations:
  - `InfoGeometry.Canonical.ConformalUnification.ConformalInference.dilation_eq_half_sub_mp_projectors`
  - `InfoGeometry.Canonical.ConformalUnification.ConformalInference.P_MP`
  - `InfoGeometry.Canonical.ConformalUnification.ConformalInference.P_MP_right`
  - `InfoGeometry.Canonical.ConformalUnification.ProjectorAgreementCertifiedConformalInference.rightProjector_eq_leftProjector`
- `EQC-0138` size `5` edges `4` relationKinds `{'eq': 4}`
  members: `M.canonicalEntropy`, `M.canonicalFreeEnergy`, `M.dualCoord`, `M.entropy`, `M.massieu`
  sample declarations:
  - `InfoGeometry.Potential.Thermo.InfoGeometry.LogPotential.LegendreModel.canonicalFreeEnergy_eq_scaled_entropy_energy`
  - `InfoGeometry.Potential.Thermo.InfoGeometry.LogPotential.LegendreModel.canonicalEntropy_eq_neg_entropy`
  - `InfoGeometry.Potential.Thermo.InfoGeometry.LogPotential.LegendreModel.massieu_eq_canonicalEntropy_minus_theta_energy`
  - `InfoGeometry.Potential.Thermo.InfoGeometry.LogPotential.LegendreModel.contact_balance`
- `EQC-0144` size `5` edges `4` relationKinds `{'eq': 4}`
  members: `P.curvatureScale`, `P.hbar`, `P.holonomyScale`, `P.omegaScale`, `P.rescaleHbar`
  sample declarations:
  - `PrequantumData.curvature_mul_hbar_eq_omega`
  - `PrequantumData.rescaleHbar_curvature`
  - `PrequantumData.omega_eq_hbar_mul_curvature`
  - `PrequantumData.holonomyScale_eq_omega_over_hbar`
- `EQC-0152` size `5` edges `4` relationKinds `{'eq': 4, 'iff': 1}`
  members: `S.anomalyTerm`, `S.boundary.boundaryGenerator`, `S.boundary.boundaryScale`, `S.boundary.rightBoundaryGenerator`, `S.boundary.spectralProjector`
  sample declarations:
  - `InfoGeometry.Canonical.SingularTransportSystem.anomalyTerm_eq_projector_commutator_norm`
  - `InfoGeometry.Canonical.SingularTransportSystem.boundaryGenerator_eq_projector_commutator`
  - `InfoGeometry.Canonical.SingularTransportSystem.boundaryGenerator_eq_zero_iff_projectors_commute`
  - `InfoGeometry.Canonical.SingularTransportSystem.boundaryScale_eq_projectorObstruction_norm`
  - `InfoGeometry.Canonical.SingularTransportSystem.dilation_commutator_decomposes_boundaryGenerator`
- `EQC-0003` size `4` edges `3` relationKinds `{'alias': 3}`
  members: `AdmissionDecision.asString`, `DeclRole.asString`, `Json.str`, `ProofHeadShape.asString`
  sample declarations:
  - `AdmissionDecision.asString`
  - `DeclRole.asString`
  - `ProofHeadShape.asString`
- `EQC-0011` size `4` edges `3` relationKinds `{'eq': 6}`
  members: `B.system.logDivergence`, `B.system.projectiveTerm`, `InfoGeometry.Canonical.CalabiYauBridge.IsRicciFlat`, `InfoGeometry.Canonical.RicciMongeAmpere.VacuumEinsteinEquationAt`
  sample declarations:
  - `InfoGeometry.Canonical.CalabiYauSingularTransportBridge.logDivergence_eq_singularComplement_of_unitRelativeVolume`
  - `InfoGeometry.Canonical.CalabiYauSingularTransportBridge.logDivergence_eq_projective_nilpotent_graded_of_unitRelativeVolume_of_boundaryScale_eq_zero`
  - `InfoGeometry.Canonical.CalabiYauSingularTransportBridge.isRicciFlat_and_logDivergence_eq_singularComplement_of_unitRelativeVolume_metricDerived`
  - `InfoGeometry.Canonical.CalabiYauSingularTransportBridge.isRicciFlat_and_logDivergence_eq_projective_nilpotent_graded_of_unitRelativeVolume_metricDerived_of_boundaryScale_eq_zero`
  - `InfoGeometry.Canonical.CalabiYauSingularTransportBridge.vacuumEinsteinEquation_and_logDivergence_eq_singularComplement_of_unitRelativeVolume_metricDerived`
- `EQC-0114` size `4` edges `3` relationKinds `{'eq': 3}`
  members: `InfoGeometry.Core.conjugationSymmetricLieAlgebra`, `InfoGeometry.Krein.conjugateCLM`, `S.P_minus`, `S.P_minus.comp`
  sample declarations:
  - `InfoGeometry.Canonical.NoetherInference.theta_commutes_with_operator_conjugation_of_commutes_with_involution`
  - `InfoGeometry.Canonical.NoetherInference.P_minus_conjugate_eq_of_theta_commutes`
  - `InfoGeometry.Core.Generic.SymmetricLieAlgebra.P_minus_comp_P_minus_linear`
- `EQC-0130` size `3` edges `3` relationKinds `{'eq': 5}`
  members: `K.G`, `K.GammaG`, `K.P_R`
  sample declarations:
  - `InfoGeometry.Canonical.DrazinPenroseDilationKKT.DPDKKT.two_smul_G_eq_GammaG`
  - `InfoGeometry.Canonical.GlobalChiralDecomposition.chiralHalfGap_decomposition`
  - `InfoGeometry.Canonical.GlobalChiralDecomposition.chiralRangeDomain_decomposition`
  - `InfoGeometry.Canonical.GlobalChiralDecomposition.chiral_range_domain_decomposition`
  - `InfoGeometry.Canonical.SingularDecompositionSurrogate.chiral_range_domain_decomposition`
- `EQC-0001` size `3` edges `2` relationKinds `{'alias': 2}`
  members: `A.comp`, `InfoGeometry.Canonical.TomitaTakesakiRealStandardForm.IsAntilinearWrt`, `InfoGeometry.Canonical.TomitaTakesakiRealStandardForm.IsLinearWrt`
  sample declarations:
  - `InfoGeometry.Canonical.TomitaTakesakiRealStandardForm.IsAntilinearWrt`
  - `InfoGeometry.Canonical.TomitaTakesakiRealStandardForm.IsLinearWrt`
- `EQC-0007` size `3` edges `2` relationKinds `{'eq': 1, 'alias': 1}`
  members: `B.character`, `B.defect`, `InfoGeometry.Canonical.ExactAbelianizingBridge.toDefective`
  sample declarations:
  - `InfoGeometry.Canonical.DefectiveAbelianizingBridge.map_mul`
  - `InfoGeometry.Canonical.ExactAbelianizingBridge.toDefective`
- `EQC-0009` size `3` edges `2` relationKinds `{'alias': 2}`
  members: `B.gaugeOf`, `InfoGeometry.Canonical.WeylGaugeField.transform`, `InfoGeometry.Canonical.transformByPotential`
  sample declarations:
  - `InfoGeometry.Canonical.WeylGaugeField.transform`
  - `InfoGeometry.Canonical.transformByPotential`
- `EQC-0010` size `3` edges `2` relationKinds `{'eq': 2}`
  members: `B.rn`, `B.toExactBridge.additiveInvariant`, `B.toLogGenerator.logGen`
  sample declarations:
  - `InfoGeometry.Volume.RadonNikodym.rn_eq_additiveInvariant`
  - `InfoGeometry.Volume.RadonNikodym.rn_eq_logGenerator`
- `EQC-0018` size `3` edges `2` relationKinds `{'iff': 2}`
  members: `CBA.IsVolumePreservingPart`, `CBA.IsWeylDilationPart`, `CBA.cartanInvolution`
  sample declarations:
  - `InfoGeometry.Canonical.ConformalAlgebra.ConformalBeliefAlgebra.cartanInvolution_eq_self_iff_volumePreserving_of_gradingInvolutive`
  - `InfoGeometry.Canonical.ConformalAlgebra.ConformalBeliefAlgebra.cartanInvolution_eq_neg_self_iff_weylDilation_of_gradingInvolutive`
- `EQC-0020` size `3` edges `2` relationKinds `{'iff': 2}`
  members: `CCI.chiralAnomalyOperator`, `CCI.operatorialIncidence`, `CCI.projectorObstructionOperator`
  sample declarations:
  - `InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.operatorialIncidence_iff_chiralAnomalyOperator_zero`
  - `InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.operatorialIncidence_iff_projectorObstructionOperator_zero`
- `EQC-0023` size `3` edges `2` relationKinds `{'alias': 2}`
  members: `CI.A_MP`, `InfoGeometry.Canonical.ConformalUnification.ConformalInference.K`, `InfoGeometry.Canonical.NavierStokesBridge.modularHamiltonian`
  sample declarations:
  - `InfoGeometry.Canonical.ConformalUnification.ConformalInference.K`
  - `InfoGeometry.Canonical.NavierStokesBridge.modularHamiltonian`
- `EQC-0031` size `3` edges `2` relationKinds `{'alias': 2}`
  members: `ClaimTier.repoTheorem`, `InfoGeometry.Canonical.SYKTwoCopyInterface.connesCocycle_state_chain_owner_claim`, `InfoGeometry.Canonical.SYKTwoCopyInterface.topologicalIndexZ2_append_owner_claim`
  sample declarations:
  - `InfoGeometry.Canonical.SYKTwoCopyInterface.connesCocycle_state_chain_owner_claim`
  - `InfoGeometry.Canonical.SYKTwoCopyInterface.topologicalIndexZ2_append_owner_claim`
- `EQC-0036` size `3` edges `2` relationKinds `{'eq': 2}`
  members: `ContinuousLinearMap.adjoint`, `TG.T`, `TG.sigma`
  sample declarations:
  - `InfoGeometry.ExponentialFamily.TwistedGaussian.TwistedGaussianFamily.adjoint_T_eq_neg`
  - `InfoGeometry.ExponentialFamily.TwistedGaussian.TwistedGaussianFamily.adjoint_infoOperator`
- `EQC-0038` size `3` edges `2` relationKinds `{'eq': 2}`
  members: `DiracMetricCompatibility.canonicalDiracOfMetric`, `IST.D`, `IST.H.metricOp`
  sample declarations:
  - `InfoGeometry.Canonical.SpectralInference.InfoSpectralTriple.dirac_eq_canonicalDiracOfMetric_of_isPositive`
  - `InfoGeometry.Canonical.SpectralInference.InfoSpectralTriple.dirac_sq_eq_metric`
- `EQC-0043` size `3` edges `2` relationKinds `{'alias': 2}`
  members: `Equiv.refl`, `InfoGeometry.Canonical.Cayley.cayleyIdentityBridge`, `InfoGeometry.Canonical.Cayley.identityBridge`
  sample declarations:
  - `InfoGeometry.Canonical.Cayley.cayleyIdentityBridge`
  - `InfoGeometry.Canonical.Cayley.identityBridge`
- `EQC-0055` size `3` edges `2` relationKinds `{'alias': 2}`
  members: `InfoGeometry.Canonical.BottDirac.Endomorphism`, `InfoGeometry.Causal.V`, `InfoGeometry.Projective.ray`
  sample declarations:
  - `InfoGeometry.Canonical.BottDirac.Endomorphism`
  - `InfoGeometry.Projective.ray`
- `EQC-0059` size `3` edges `2` relationKinds `{'alias': 2}`
  members: `InfoGeometry.Canonical.Cayley.cayleyNegationCompatibleGeometry`, `InfoGeometry.Canonical.Cayley.quadraticDualFlat`, `InfoGeometry.Canonical.Cayley.quadraticPotential`
  sample declarations:
  - `InfoGeometry.Canonical.Cayley.cayleyNegationCompatibleGeometry`
  - `InfoGeometry.Canonical.Cayley.quadraticDualFlat`

## Unresolved Head Tokens
- `EndH`: `15`
- `commutator`: `13`
- `anticommutator`: `9`
- `fenchelGap`: `9`
- `MP_Projector`: `9`
- `fixedSubgroup`: `6`
- `DoubledSpace`: `6`
- `cartanSymmetryOfInvolutiveMulAut`: `5`
- `FinProb`: `5`
- `spectralProjector`: `5`
- `J`: `5`
- `Mat`: `5`
- `Drazin_Projector`: `5`
- `anomaly`: `4`
- `chiralAnomaly`: `4`
- `superHamiltonian`: `4`
- `jOp`: `4`
- `epsOp`: `4`
- `cartanSymmetry`: `3`
- `symmetricSpaceOfCartan`: `3`
- `potential`: `3`
- `ChiralAnomaly`: `3`
- `metricProjector`: `3`
- `chiralAnomalyOperator`: `3`
- `oneOp`: `3`
- `toLogGenerator`: `3`
- `rightProjector`: `3`
- `leftProjector`: `3`
- `Alg`: `3`
- `Spinodal`: `3`
- `IsOdd`: `3`
- `IsEven`: `3`
- `IsKreinSkewAdjoint`: `3`
- `Gauge`: `3`
- `HasPhaseParity`: `2`
- `leftChiralAnomaly`: `2`
- `leftChiralAnomalyOperator`: `2`
- `rightChiralAnomalyOperator`: `2`
- `P_D`: `2`
- `RoutingMode`: `2`
- `RoutingLabel`: `2`
- `projectorMismatch`: `2`
- `comm`: `2`
- `Op`: `2`
- `KLinear`: `2`
- `KAntilinear`: `2`
- `Matn`: `2`
- `Cl11`: `2`
- `Carrier`: `2`
- `clmComm`: `2`
- `splitQuatBasis`: `2`
- `Spinodal2D`: `2`
- `symmetricPairOfInvolutiveMulAut`: `2`
- `eGeodesicConvex`: `2`
- `val`: `2`
- `ofLp`: `2`
- `afterAttention`: `2`
- `run`: `2`
- `GaugeEquivalent`: `2`
- `gaugeSetoid`: `2`

## Notes
- This report is lexical and intentionally conservative.
- For closure promotion, pair it with translation-registry and architecture audits.
