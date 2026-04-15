# Sorry-Equivalence Report

Total theorems analysed: **9399**

## Classification Summary

| Class | Count | % |
|-------|------:|--:|
| dead | 3279 | 34.9% |
| dead-endpoint | 2208 | 23.5% |
| type-only | 5 | 0.1% |
| forwarding | 265 | 2.8% |
| live | 3642 | 38.7% |

**Sorry-equivalent (dead + type-only):** 5492 (58.4%)
**Wrappers (forwarding):** 265
**Load-bearing (live):** 3642

## Top Files by Dead Theorem Count

| File | Dead | Type-only | Forwarding | Live | Total |
|------|-----:|----------:|-----------:|-----:|------:|
| lean/InfoGeometry/Quantum/RealMajorana.lean | 65 | 0 | 1 | 52 | 118 |
| lean/InfoGeometry/Canonical/SinkhornFoundation.lean | 54 | 0 | 2 | 27 | 83 |
| lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean | 52 | 0 | 1 | 31 | 84 |
| lean/InfoGeometry/Quantum/HestenesKahler.lean | 52 | 0 | 0 | 13 | 65 |
| lean/InfoGeometry/Canonical/BerryConnection.lean | 50 | 0 | 1 | 14 | 65 |
| lean/InfoGeometry/Core/SymmetricLie.lean | 50 | 0 | 5 | 29 | 84 |
| lean/InfoGeometry/Canonical/ModularSuperchargeClosure.lean | 47 | 0 | 1 | 39 | 87 |
| lean/InfoGeometry/Quantum/ModularAnomaly.lean | 47 | 0 | 0 | 48 | 95 |
| lean/InfoGeometry/Quantum/RealMajoranaCategory.lean | 44 | 0 | 0 | 38 | 82 |
| lean/InfoGeometry/MaxEnt/Jaynes.lean | 40 | 0 | 1 | 8 | 49 |
| lean/InfoGeometry/Canonical/TransportLieDerivative.lean | 39 | 0 | 1 | 23 | 63 |
| lean/InfoGeometry/Geometry/DualFlat.lean | 39 | 0 | 2 | 14 | 55 |
| lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean | 38 | 2 | 1 | 58 | 99 |
| lean/InfoGeometry/Canonical/ConformalProjectorCore.lean | 37 | 0 | 2 | 41 | 80 |
| lean/InfoGeometry/Canonical/MongeAmpereDualSheetBridge.lean | 37 | 0 | 0 | 29 | 66 |
| lean/InfoGeometry/LLM/TransformerArchitecture.lean | 37 | 0 | 0 | 3 | 40 |
| lean/InfoGeometry/Thermal/FiniteMatrix.lean | 37 | 0 | 1 | 3 | 41 |
| lean/InfoGeometry/Canonical/IBUpdate.lean | 36 | 0 | 0 | 18 | 54 |
| lean/InfoGeometry/Canonical/RelationalInformationDynamics.lean | 36 | 0 | 1 | 11 | 48 |
| lean/InfoGeometry/Canonical/RicciMongeAmpere.lean | 36 | 0 | 0 | 18 | 54 |
| lean/InfoGeometry/Clifford/PhaseSpaceGeneralizedMetric.lean | 34 | 0 | 2 | 17 | 53 |
| lean/InfoGeometry/Canonical/ThermodynamicGenerator.lean | 33 | 0 | 0 | 19 | 52 |
| lean/InfoGeometry/Canonical/BogoliubovFockSuper.lean | 32 | 0 | 2 | 30 | 64 |
| lean/InfoGeometry/Krein/HilbertBridge.lean | 32 | 0 | 2 | 2 | 36 |
| lean/InfoGeometry/Canonical/GrandCanonicalExperts.lean | 31 | 0 | 0 | 11 | 42 |
| lean/InfoGeometry/Canonical/StandardFormCore.lean | 31 | 0 | 1 | 6 | 38 |
| lean/InfoGeometry/Core/Involution.lean | 31 | 0 | 3 | 21 | 55 |
| lean/InfoGeometry/Canonical/RelativeModularSingularization.lean | 30 | 0 | 3 | 16 | 49 |
| lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean | 30 | 0 | 0 | 28 | 58 |
| lean/InfoGeometry/Canonical/DrazinInfiniteCore.lean | 29 | 0 | 3 | 9 | 41 |

## Dead Theorems With Docstrings (Possible Capstones)

- `InfoGeometry.Analytic.deriv2_logSumExp_eq_softmaxVariance` (lean/InfoGeometry/ExponentialFamily/Analytic/Softmax.lean:248)
  > Main second-derivative identity: `deriv²(logSumExp) = Var_p[a]`.
- `InfoGeometry.Analytic.deriv_logSumExp_eq_firstMoment_div_partition` (lean/InfoGeometry/ExponentialFamily/Analytic/Softmax.lean:147)
  > First derivative: `(log Z)'(θ) = Z'(θ)/Z(θ) = M₁(θ)/Z(θ)`.
- `InfoGeometry.Analytic.deriv_logSumExp_eq_softmaxMean` (lean/InfoGeometry/ExponentialFamily/Analytic/Softmax.lean:185)
  > Main first-derivative identity: `deriv(logSumExp) = E_p[a]`.
- `InfoGeometry.Analytic.logSumExp_eq_log_partition` (lean/InfoGeometry/ExponentialFamily/Analytic/Softmax.lean:138)
  > `logSumExp w a = log(Z)` with `Z = softmaxPartition`.
- `InfoGeometry.Analytic.softmaxMean_eq_firstMoment_div_partition` (lean/InfoGeometry/ExponentialFamily/Analytic/Softmax.lean:161)
  > `E_p[a] = M₁/Z`.
- `InfoGeometry.Analytic.softmaxSecondMoment_eq_secondMomentUnnormalized_div_partition` (lean/InfoGeometry/ExponentialFamily/Analytic/Softmax.lean:177)
  > Normalized second moment equals `M₂/Z`.
- `InfoGeometry.Architecture.SpinFactor.spinFactorPotential_well_defined` (lean/InfoGeometry/Architecture/SpinFactor.lean:47)
  > The potential is well-defined and finite strictly inside the domain.
- `InfoGeometry.Architecture.SpinFactor.spinFactorPotential_zero` (lean/InfoGeometry/Architecture/SpinFactor.lean:54)
  > We evaluate the potential at the zero-point origin of the phase space.
- `InfoGeometry.Architecture.SpinFactor.spinFactor_poly_identity` (lean/InfoGeometry/Architecture/SpinFactor.lean:27)
  > Identity: 1 - 2‖x‖² + ‖x‖⁴ = (1 - ‖x‖²)².
This simplification is critical for deriving the Hessian and mass gap effectiv
- `InfoGeometry.Canonical.AQFTOperatorInterface.ibWeightedKMSClosure_of_jointKernel_commutator` (lean/InfoGeometry/Canonical/AQFTOperatorEndpoints.lean:58)
  > Constructive thermal payload:
derive weighted Sinkhorn-KMS closure from IB dynamics through the
joint-kernel/commutator 
- `InfoGeometry.Canonical.ActionDuality.einsteinHilbertAction_and_zeroGap_of_compatible` (lean/InfoGeometry/Canonical/ActionDuality.lean:54)
  > Compatible basepoint action rewrite together with zero Fenchel gap at the same
dual covector.
- `InfoGeometry.Canonical.ActionDuality.einsteinHilbertAction_eq_neg_six_dual_pairing_sub_dual_of_compatible` (lean/InfoGeometry/Canonical/ActionDuality.lean:34)
  > At a compatible basepoint `θ₀`, the reduced Einstein-Hilbert action proxy is
exactly `-6` times the dual pairing minus t
- `InfoGeometry.Canonical.AlgebraicStationarity.isAlgebraicallyStationary_of_central` (lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:223)
  > Central observables are algebraically stationary in every state.
- `InfoGeometry.Canonical.AlgebraicStationarity.isAlgebraicallyStationary_zero` (lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:201)
  > The zero observable is algebraically stationary in every state.
- `InfoGeometry.Canonical.AlgebraicStationarity.isStateAlgebraicallyStationary_iff_algebraicEinsteinBalance` (lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:118)
  > State algebraic stationarity is equivalent to exact gauge/source cancellation in
expectation.
- `InfoGeometry.Canonical.AlgebraicStationarity.isStateAlgebraicallyStationary_iff_generatorStationarity` (lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:105)
  > State algebraic stationarity is exactly stationarity along the derived modular
generator at the chosen state.
- `InfoGeometry.Canonical.AlgebraicStationarity.modularCurvatureExpectation_eq_zero_of_phaseResponseStationary` (lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:258)
  > If the phase response of `D` is stationary under the internal phase axis `K`,
then the expectation of the modular curvat
- `InfoGeometry.Canonical.AlgebraicStationarity.operatorInformationFirstVariation_neg_left` (lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:179)
  > Negating the generator negates the induced commutator variation.
- `InfoGeometry.Canonical.AlgebraicStationarity.operatorInformationFirstVariation_neg_right` (lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:190)
  > Negating the observable negates the induced commutator variation.
- `InfoGeometry.Canonical.AlgebraicStationarity.phaseAxisResponse_eq_neg_KVariation` (lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:232)
  > The phase-axis response is the negative `K`-variation of the observable.
- `InfoGeometry.Canonical.AlgebraicStationarity.starCertifiedEinsteinAnomalyStationary_iff_projectorObstructionStationary_of_projectorAgreement` (lean/InfoGeometry/Canonical/AlgebraicStationarity.lean:140)
  > Projector-agreement closure turns Einstein-anomaly stationarity into
projector-obstruction stationarity on the same obse
- `InfoGeometry.Canonical.AnalyticalIndex.FullThermoGeoIndexCapstone.geometricAlgebraicState` (lean/InfoGeometry/Canonical/AnalyticalIndexCapstone.lean:103)
  > Lemma `FullThermoGeoIndexCapstone`.
- `InfoGeometry.Canonical.AnalyticalIndex.FullThermoGeoIndexCapstone.thermodynamicKMSState` (lean/InfoGeometry/Canonical/AnalyticalIndexCapstone.lean:115)
  > Lemma `FullThermoGeoIndexCapstone`.
- `InfoGeometry.Canonical.AnalyticalIndex.SinkhornKMSCapstone.kmsState` (lean/InfoGeometry/Canonical/AnalyticalIndexCapstone.lean:38)
  > Lemma `SinkhornKMSCapstone`.
- `InfoGeometry.Canonical.AnalyticalIndex.SinkhornRicciIndexInvariant.of_cl11BottConjugacy` (lean/InfoGeometry/Canonical/AnalyticalIndexCoupled.lean:126)
  > Derived constructor for the `Cl(1,1)` Bott lift using primitive flow-conjugacy
conditions on the base space.

This is a 
- `InfoGeometry.Canonical.AnalyticalIndex.SinkhornRicciIndexInvariant.of_modularCliffordTransport` (lean/InfoGeometry/Canonical/AnalyticalIndexCoupled.lean:63)
  > Derived constructor using modular-flow / Clifford-bundle transport conditions
for the chiral slices.
- `InfoGeometry.Canonical.AnalyticalIndex.SinkhornRicciIndexInvariant.of_modularCliffordTransport_components` (lean/InfoGeometry/Canonical/AnalyticalIndexCoupled.lean:91)
  > Primitive-condition form of the coupled Sinkhorn/Ricci/index invariant:
modular/Clifford transport is supplied as explic
- `InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex_eq_of_chiralParts_eq` (lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:254)
  > Lemma `analyticalIndex_eq_of_chiralParts_eq`.
- `InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex_eq_zero_time_of_cartanConjugate` (lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:997)
  > Pointwise analytical-index invariance along exact Cartan exponential transport.
- `InfoGeometry.Canonical.AnalyticalIndex.chiralPartMinus_eq_projectorPlus_comp_of_anticommute` (lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:215)
  > If `D ∘ Γ + Γ ∘ D = 0`, then `D` carries the negative split into the positive
split: `D ∘ P₋ = P₊ ∘ D`.
- `InfoGeometry.Canonical.AnalyticalIndex.chiralPartPlus_eq_projectorMinus_comp_of_anticommute` (lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:194)
  > If `D ∘ Γ + Γ ∘ D = 0`, then `D` carries the positive split into the negative
split: `D ∘ P₊ = P₋ ∘ D`.
- `InfoGeometry.Canonical.AnalyticalIndex.chiralProjectorMinus_comp_self_of_square_eq_id` (lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:168)
  > Under `Γ ∘ Γ = Id`, `P₋` is an idempotent projector.
- `InfoGeometry.Canonical.AnalyticalIndex.chiralProjectorPlus_comp_self_of_square_eq_id` (lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:142)
  > Under `Γ ∘ Γ = Id`, `P₊` is an idempotent projector.
- `InfoGeometry.Canonical.AnalyticalIndex.chiralSliceIsoAlong_of_noZeroEigenCrossing_path` (lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:498)
  > Path-level no-zero-eigenvalue-crossing closure:
chiral-slice isomorphism is derived via the no-zero-eigenvalue-crossing 
- `InfoGeometry.Canonical.AnalyticalIndex.cl11BottAnalyticalIndex_eq_neg_of_projectiveJ` (lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:1256)
  > Exact `J`-transport on the Bott root preserves the analytical index under the
sign-twist `(D, Γ) ↦ (-D, -Γ)`.
- `InfoGeometry.Canonical.AnalyticalIndex.cl11BottAnalyticalIndex_eq_zero_time_of_conjugacy` (lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:1278)
  > Pointwise `Cl(1,1)` Bott analytical-index invariance:
base-space chiral conjugacy identifies each lifted Bott index with
- `InfoGeometry.Canonical.AnalyticalIndex.cl11BottDirac_comp_cl11GlobalGrading_add_cl11GlobalGrading_comp_cl11BottDirac` (lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:1055)
  > Exact lifted chiral law for the `Cl(1,1)` Bott root:
if the second-factor Dirac/grading pair anticommutes, then the lift
- `InfoGeometry.Canonical.AnalyticalIndex.cl11_bottDirac_sq_eq_zero_of_laplacian_zero` (lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:1307)
  > Theorem `cl11_bottDirac_sq_eq_zero_of_laplacian_zero`.
- `InfoGeometry.Canonical.AnalyticalIndex.fullThermoGeoIndexCapstone_of_states` (lean/InfoGeometry/Canonical/AnalyticalIndexCapstone.lean:87)
  > Canonical constructor for the full capstone package from the two state-level
components.
- `InfoGeometry.Canonical.AnalyticalIndex.indexInvariantAlong_of_noZeroEigenCrossing_path` (lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean:827)
  > Path-level no-zero-eigenvalue-crossing index invariance:
obtained from no-zero-eigenvalue crossing along the path.
- `InfoGeometry.Canonical.AnalyticalIndex.sinkhornIterate_sinkhornKMSCapstone_of_closure` (lean/InfoGeometry/Canonical/AnalyticalIndexCapstone.lean:48)
  > Constructive iterate specialization from closure (primary closure-first form).
- `InfoGeometry.Canonical.AnomalyGauge.anomaly_generates_isometry` (lean/InfoGeometry/Canonical/AnomalyGauge.lean:89)
  > Legacy name for the infinitesimal-isometry statement.
- `InfoGeometry.Canonical.AnomalyInflow.anomalyInflowClosure` (lean/InfoGeometry/Canonical/AnomalyInflow.lean:75)
  > Theorem `anomalyInflowClosure`.
- `InfoGeometry.Canonical.Attention.euclideanAttentionWeights_sum_one` (lean/InfoGeometry/Canonical/AttentionEuclidean.lean:58)
  > Theorem: Standard Attention is rigorously normalized.
- `InfoGeometry.Canonical.Attention.exists_perm_decomposition_of_bistochastic_polarizedPlusAttention` (lean/InfoGeometry/Canonical/AttentionPolarizedSinkhornBridge.lean:95)
  > A column-balanced polarized split attention matrix admits a Birkhoff-von Neumann
permutation decomposition.
- `InfoGeometry.Canonical.Attention.lorentzianAttentionWeights_sum_one` (lean/InfoGeometry/Canonical/AttentionSplit.lean:47)
  > Theorem: Lorentzian Attention is rigorously normalized.
- `InfoGeometry.Canonical.Attention.partition_polarizedPlusParams_eq_logitSum` (lean/InfoGeometry/Canonical/AttentionPolarizedGibbsBridge.lean:58)
  > The grand-canonical partition of the polarized split energy is exactly the
normalizing sum of exponentiated polarized at
- `InfoGeometry.Canonical.Attention.polarizedPlusAttentionHead_eq_euclideanAttentionHead_of_constantKeyNorm` (lean/InfoGeometry/Canonical/AttentionPolarizedSplit.lean:168)
  > Under constant key norm, the positive-sheet split attention head is exactly Euclidean.
- `InfoGeometry.Canonical.Attention.polarizedPlusAttentionHead_eq_gibbsExpectation` (lean/InfoGeometry/Canonical/AttentionPolarizedGibbsBridge.lean:117)
  > The positive-sheet split attention head is the Gibbs expectation of the values
under the polarized split grand-canonical
- `InfoGeometry.Canonical.Attention.polarizedPlusAttentionMatrix_mem_rowStochastic` (lean/InfoGeometry/Canonical/AttentionPolarizedSinkhornBridge.lean:64)
  > The polarized split attention matrix is row-stochastic by Gibbs normalization.

## Forwarding Theorems (Thin Wrappers)

Total: 265

- `InfoGeometry.Analytic.deriv_logSumExpMoment1` → `InfoGeometry.Analytic.hasDerivAt_logSumExpMoment1` (lean/InfoGeometry/ExponentialFamily/Analytic/LogSumExp.lean:261)
- `InfoGeometry.Analytic.deriv_logSumExpPartition` → `InfoGeometry.Analytic.hasDerivAt_logSumExpPartition` (lean/InfoGeometry/ExponentialFamily/Analytic/LogSumExp.lean:234)
- `InfoGeometry.Analytic.hasDerivAt_logSumExpMoment1` → `InfoGeometry.Analytic.hasDerivAt_logSumExpPartition_term` (lean/InfoGeometry/ExponentialFamily/Analytic/LogSumExp.lean:240)
- `InfoGeometry.Analytic.hasDerivAt_logSumExpPartition` → `InfoGeometry.Analytic.hasDerivAt_logSumExpPartition_term` (lean/InfoGeometry/ExponentialFamily/Analytic/LogSumExp.lean:223)
- `InfoGeometry.Analytic.logSumExpScaledBregman_eq_eps_mul_KL` → `InfoGeometry.Analytic.logSumExpScaledKL_eq_inv_eps_mul_bregman` (lean/InfoGeometry/ExponentialFamily/Analytic/LogSumExp.lean:567)
- `InfoGeometry.Analytic.logSumExpScaledPartition_pos` → `InfoGeometry.Analytic.logSumExp_sum_pos` (lean/InfoGeometry/ExponentialFamily/Analytic/LogSumExp.lean:146)
- `InfoGeometry.Analytic.logSumExpScaledWeight_sum_one` → `InfoGeometry.Analytic.logSumExpWeight_sum_one` (lean/InfoGeometry/ExponentialFamily/Analytic/LogSumExp.lean:188)
- `InfoGeometry.Analytic.logSumExpWeight_pos` → `InfoGeometry.Analytic.logSumExp_sum_pos` (lean/InfoGeometry/ExponentialFamily/Analytic/LogSumExp.lean:177)
- `InfoGeometry.Analytic.logSumExpWeight_sum_one` → `InfoGeometry.Analytic.logSumExp_sum_pos` (lean/InfoGeometry/ExponentialFamily/Analytic/LogSumExp.lean:155)
- `InfoGeometry.Analytic.logSumExp_contDiff` → `InfoGeometry.Analytic.logSumExp_sum_pos` (lean/InfoGeometry/ExponentialFamily/Analytic/LogSumExp.lean:613)
- `InfoGeometry.Analytic.logSumExp_deriv_eq_mean` → `InfoGeometry.Analytic.logSumExp_deriv_eq_ratio` (lean/InfoGeometry/ExponentialFamily/Analytic/LogSumExp.lean:335)
- `InfoGeometry.Analytic.softmaxProb_pos` → `InfoGeometry.Analytic.logSumExpWeight_pos` (lean/InfoGeometry/ExponentialFamily/Analytic/Softmax.lean:46)
- `InfoGeometry.Analytic.softmaxProb_sum_one` → `InfoGeometry.Analytic.logSumExpWeight_sum_one` (lean/InfoGeometry/ExponentialFamily/Analytic/Softmax.lean:51)
- `InfoGeometry.Architecture.symmetry_self` → `InfoGeometry.Architecture.SymmetricSpace.symm_fixpoint` (lean/InfoGeometry/Architecture/SymmetricSpace.lean:27)
- `InfoGeometry.Architecture.symmetry_symmetry` → `InfoGeometry.Architecture.SymmetricSpace.symm_involutive` (lean/InfoGeometry/Architecture/SymmetricSpace.lean:20)
- `InfoGeometry.Canonical.AdditiveLinearization.map_mul_apply` → `InfoGeometry.Canonical.AdditiveLinearization.map_mul` (lean/InfoGeometry/Canonical/MultiplicativeToAdditiveBridge.lean:90)
- `InfoGeometry.Canonical.BekensteinBound.topologicalBekensteinBound_of_sinkhornTrajectory` → `InfoGeometry.Canonical.BekensteinBound.trajectoryRNBarrier_nonneg` (lean/InfoGeometry/Canonical/BekensteinBound.lean:41)
- `InfoGeometry.Canonical.BerryPhase.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace` → `InfoGeometry.Krein.instL2Complete` (lean/InfoGeometry/Canonical/BerryConnection.lean:30)
- `InfoGeometry.Canonical.BogoliubovFockSuper.fockAnticommutator_symm` → `InfoGeometry.Canonical.BogoliubovFockSuper.anticommutator_symm` (lean/InfoGeometry/Canonical/BogoliubovFockSuper.lean:369)
- `InfoGeometry.Canonical.BogoliubovFockSuper.fockCommutator_swap` → `InfoGeometry.Canonical.BogoliubovFockSuper.commutator_swap` (lean/InfoGeometry/Canonical/BogoliubovFockSuper.lean:380)
- `InfoGeometry.Canonical.BogoliubovProjectorTransport.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace` → `InfoGeometry.Krein.instL2Complete` (lean/InfoGeometry/Canonical/BogoliubovProjectorTransport.lean:24)
- `InfoGeometry.Canonical.BogoliubovProjectorTransport.spectralMinusProj_comp_complex_i` → `InfoGeometry.Canonical.BogoliubovProjectorTransport.spectralMinusProj_comp_K` (lean/InfoGeometry/Canonical/BogoliubovProjectorTransport.lean:148)
- `InfoGeometry.Canonical.BogoliubovProjectorTransport.spectralMinusProj_comp_modular_j` → `InfoGeometry.Canonical.BogoliubovProjectorTransport.spectralMinusProj_comp_J` (lean/InfoGeometry/Canonical/BogoliubovProjectorTransport.lean:114)
- `InfoGeometry.Canonical.BogoliubovProjectorTransport.spectralPlusProj_comp_complex_i` → `InfoGeometry.Canonical.BogoliubovProjectorTransport.spectralPlusProj_comp_K` (lean/InfoGeometry/Canonical/BogoliubovProjectorTransport.lean:131)
- `InfoGeometry.Canonical.BogoliubovProjectorTransport.spectralPlusProj_comp_modular_j` → `InfoGeometry.Canonical.BogoliubovProjectorTransport.spectralPlusProj_comp_J` (lean/InfoGeometry/Canonical/BogoliubovProjectorTransport.lean:97)
- `InfoGeometry.Canonical.BogoliubovTransport.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace` → `InfoGeometry.Krein.instL2Complete` (lean/InfoGeometry/Canonical/BogoliubovTransport.lean:41)
- `InfoGeometry.Canonical.BogoliubovVielbein.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace` → `InfoGeometry.Krein.instL2Complete` (lean/InfoGeometry/Canonical/BogoliubovVielbein.lean:33)
- `InfoGeometry.Canonical.CertifiedInverseKernel.drazinCoreProj_idempotent` → `InfoGeometry.Canonical.CertifiedInverseKernel.spectralProjector_idempotent` (lean/InfoGeometry/Canonical/EPDefectAlgebra.lean:55)
- `InfoGeometry.Canonical.CertifiedInverseKernel.geometricCartanGenerator_eq_two_smul_dilationGenerator` → `InfoGeometry.Canonical.CertifiedInverseKernel.mpChiralGap_eq_two_smul_dilationGap` (lean/InfoGeometry/Canonical/DrazinPenroseDilationAlgebra.lean:68)
- `InfoGeometry.Canonical.CertifiedInverseKernel.spectralProjector_add_spectralComplementaryProjector` → `InfoGeometry.Canonical.InverseKernel.spectralProjector_add_spectralComplementaryProjector` (lean/InfoGeometry/Canonical/InverseKernelAlgebra.lean:126)
- `InfoGeometry.Canonical.ConformalAlgebra.ConformalBeliefAlgebra.scale_anomaly_breaks_weight_closure` → `InfoGeometry.Canonical.ConformalAlgebra.ConformalBeliefAlgebra.scale_anomaly_emergence` (lean/InfoGeometry/Canonical/ConformalAlgebra.lean:89)
- `InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.instCompleteSpaceContinuousLinearMapRealIdDoubledSpace` → `InfoGeometry.Krein.instL2Complete` (lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean:25)
- `InfoGeometry.Canonical.ConformalUnification.ProjectorAgreementCertifiedConformalInference.rightProjector_eq_leftProjector` → `InfoGeometry.Canonical.ConformalUnification.ProjectorAgreementCertifiedConformalInference.projectorAgreement` (lean/InfoGeometry/Canonical/ConformalProjectorCore.lean:251)
- `InfoGeometry.Canonical.ConformalUnification.StarCertifiedConformalInference.leftChiralAnomalyOperator_star_eq_neg` → `InfoGeometry.Canonical.ConformalUnification.StarCertifiedConformalInference.chiralAnomalyOperator_star_eq_neg` (lean/InfoGeometry/Canonical/ConformalProjectorCore.lean:390)
- `InfoGeometry.Canonical.DefectiveAbelianizingBridge.map_mul` → `InfoGeometry.Canonical.DefectiveAbelianizingBridge.map_mul_defect` (lean/InfoGeometry/Canonical/MultiplicativeToAdditiveBridge.lean:55)
- `InfoGeometry.Canonical.DensityWeightIntertwinerBridge.densityWeightPhaseAxis_eq_dilationOperator` → `InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_eq_dilationOperator` (lean/InfoGeometry/Canonical/DensityWeightIntertwinerBridge.lean:143)
- `InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection_pow_succ` → `InfoGeometry.Canonical.Drazin.IsDrazinInverse.complementaryProjection_is_idempotent` (lean/InfoGeometry/Canonical/DrazinCoreFlow.lean:102)
- `InfoGeometry.Canonical.Drazin.IsDrazinInverse.power_le` → `InfoGeometry.Canonical.Drazin.IsDrazinInverse.power` (lean/InfoGeometry/Canonical/Drazin.lean:98)
- `InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection_is_idempotent` → `InfoGeometry.Canonical.Drazin.IsDrazinInverse.idempotent` (lean/InfoGeometry/Canonical/Drazin.lean:47)
- `InfoGeometry.Canonical.Drazin.IsDrazinInverse.projection_mul_eq_mul_projection` → `InfoGeometry.Canonical.Drazin.IsDrazinInverse.comm` (lean/InfoGeometry/Canonical/DrazinCoreFlow.lean:29)

## Most-Depended-On Theorems (by reverse value-edge count)

| Theorem | Reverse-value uses | Module |
|---------|-------------------:|--------|
| `InfoGeometry.Krein.instL2Complete` | 888 | InfoGeometry.Krein.KreinSpace |
| `InfoGeometry.Krein.DoubledSpace.ext` | 159 | InfoGeometry.Krein.DoubledSpace |
| `InfoGeometry.Krein.complex_i_apply` | 130 | InfoGeometry.Krein.DoubledSpace |
| `InfoGeometry.Clifford.splitQ11_apply` | 42 | InfoGeometry.Clifford.SplitQ11 |
| `InfoGeometry.Canonical.BogoliubovFockSuper.superBracket_odd_odd` | 31 | InfoGeometry.Canonical.BogoliubovFockSuper |
| `InfoGeometry.Canonical.CertifiedInverseKernel.hDrazin` | 30 | InfoGeometry.Canonical.CertifiedInverseKernel |
| `InfoGeometry.Krein.SplitQuadraticSheets.fst_plusPoint` | 28 | InfoGeometry.Krein.SplitQuadraticSheets |
| `InfoGeometry.Krein.SplitQuadraticSheets.snd_minusPoint` | 28 | InfoGeometry.Krein.SplitQuadraticSheets |
| `InfoGeometry.Krein.SplitQuadraticSheets.fst_minusPoint` | 27 | InfoGeometry.Krein.SplitQuadraticSheets |
| `InfoGeometry.Krein.SplitQuadraticSheets.snd_plusPoint` | 26 | InfoGeometry.Krein.SplitQuadraticSheets |
| `InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge.toDoubledCopyRho_apply` | 25 | InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge |
| `InfoGeometry.PositiveMeasure.pos` | 24 | InfoGeometry.PositiveMeasure |
| `InfoGeometry.Canonical.SuperchargeCARCCRBridge.cptSuperchargeOp_eq_complex_i` | 21 | InfoGeometry.Canonical.SuperchargeCARCCRBridge |
| `InfoGeometry.Krein.cl11Rep_ι_apply` | 21 | InfoGeometry.Krein.Representation |
| `InfoGeometry.Canonical.BogoliubovTransport.instIsTopologicalRingContinuousLinearMapRealIdDoubledSpace` | 18 | InfoGeometry.Canonical.BogoliubovTransport |
| `InfoGeometry.Canonical.CertifiedInverseKernel.spectralProjector_idempotent` | 16 | InfoGeometry.Canonical.CertifiedInverseKernel |
| `InfoGeometry.Canonical.RelativePotentialScalarBridge.scalarModularPotential_eq_neg_log` | 14 | InfoGeometry.Canonical.RelativePotentialScalarBridge |
| `InfoGeometry.Canonical.BogoliubovClosedForms.KRotation_apply` | 13 | InfoGeometry.Canonical.BogoliubovClosedForms |
| `InfoGeometry.Canonical.GeneralizedMetricCore.tomitaGeneralizedMetricSeed_minusProjector_eq_spectralMinusProj` | 13 | InfoGeometry.Canonical.GeneralizedMetricCore |
| `InfoGeometry.Canonical.GeneralizedMetricCore.tomitaGeneralizedMetricSeed_plusProjector_eq_spectralPlusProj` | 13 | InfoGeometry.Canonical.GeneralizedMetricCore |
| `InfoGeometry.Canonical.IB.baScoreFrozen_ne_top` | 13 | InfoGeometry.Canonical.IBBase |
| `InfoGeometry.Krein.PolarizedSector.spectralMinusProj_apply_eq_minusPoint` | 13 | InfoGeometry.Krein.PolarizedSector |
| `InfoGeometry.Krein.PolarizedSector.spectralPlusProj_apply_eq_plusPoint` | 13 | InfoGeometry.Krein.PolarizedSector |
| `InfoGeometry.Krein.spectral_epsilon_involution` | 13 | InfoGeometry.Krein.DoubledSpace |
| `InfoGeometry.Canonical.RelativeModularPotential.toRelationalInformationDatum_comparisonGeneratorMetric_apply` | 12 | InfoGeometry.Canonical.RelativeModularPotential |
| `InfoGeometry.Canonical.StateDependentTransport.stateQGTPhaseReadout_eq_metric_comp_complex_i` | 12 | InfoGeometry.Canonical.StateDependentTransport |
| `InfoGeometry.PositiveMeasure.generalizedKL_eq_klLike_add_Z` | 12 | InfoGeometry.Projective.GaugeReduction |
| `InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorPhase_apply_eq_comp_complex_i` | 11 | InfoGeometry.Canonical.RelativeModularPotential |
| `InfoGeometry.Canonical.RestrictedVolumeCharacter.dualSheetLift_eq_dualSheetPairLift_same` | 11 | InfoGeometry.Canonical.RestrictedVolumeCharacter |
| `InfoGeometry.Canonical.SplitCliffordHeadLift.headNullMinusTensor_eq_formula` | 11 | InfoGeometry.Canonical.SplitCliffordHeadLift |

## Policy

- A **dead** theorem can be sorry'd (or deleted) with zero downstream impact.
- A **dead-endpoint** uses live infrastructure but nobody consumes it — likely a capstone or orphan.
- A **type-only** theorem appears in statement scaffolding but never in any proof body.
- A **forwarding** theorem's proof delegates to exactly one other theorem — candidate for inlining.
- A **live** theorem is genuinely load-bearing: downstream proofs depend on it.
- Dead theorems with docstrings may be intentional capstone results worth keeping.
- Forwarding theorems are the prime candidates for wrapper elimination.
