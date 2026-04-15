# ConformalUnification Topological Patch

Purpose:
- extract a clean local module manifold around the seed hotspot
- separate constructive support modules from reverse consumer modules
- provide exact cross-module declaration interfaces for LLM bridge generation

## Seed Pressure
- seed module: `InfoGeometry.Canonical.ConformalUnification`
- burn-down rank: **1**
- burn-down score: **2607.829**
- dominant pressure: `surrogate_or_vacuous`
- action: direct constructive replacement
- mix (H/P/S): `0/0/96`

## Support Cone
- `InfoGeometry.Canonical.CertifiedInverseKernel` weight=`83` dominant=`likely_constructive`
- `InfoGeometry.Canonical.GrandCanonicalExperts` weight=`24` dominant=`likely_constructive`
- `InfoGeometry.Canonical.Singular` weight=`23` dominant=`likely_constructive`
- `InfoGeometry.Canonical.MoorePenrose` weight=`16` dominant=`likely_constructive`
- `InfoGeometry.Canonical.RicciMongeAmpere` weight=`11` dominant=`likely_constructive`
- `InfoGeometry.Canonical.Drazin` weight=`4` dominant=`likely_constructive`
- `InfoGeometry.Canonical.ChiralEinsteinBridge` weight=`4` dominant=`likely_constructive`
- `InfoGeometry.Canonical.KaehlerGeometry` weight=`1` dominant=`likely_constructive`

## Reverse Consumer Cone
- `InfoGeometry.Canonical.ConformalAlgebra` weight=`64` dominant=`surrogate_or_vacuous`
- `InfoGeometry.Canonical.WeylTransportChiralBridge` weight=`33` dominant=`likely_constructive`
- `InfoGeometry.Canonical.MasterSynthesis` weight=`23` dominant=`surrogate_or_vacuous`
- `InfoGeometry.Canonical.ChiralCliffordBridge` weight=`20` dominant=`package_reprojection`
- `InfoGeometry.Canonical.WeylInformationGauge` weight=`17` dominant=`hypothesis_bridge`
- `InfoGeometry.Canonical.AnomalyDilationBridge` weight=`14` dominant=`package_reprojection`
- `InfoGeometry.Canonical.ChiralTorsionBridge` weight=`12` dominant=`package_reprojection`
- `InfoGeometry.Canonical.ChiralAction` weight=`7` dominant=`surrogate_or_vacuous`

## Extra Frontier Neighbors
- `InfoGeometry.Canonical.Rosetta` weight=`5` dominant=`surrogate_or_vacuous` direction=`consumer`
- `InfoGeometry.Canonical.HolographicEmergence` weight=`4` dominant=`surrogate_or_vacuous` direction=`consumer`
- `InfoGeometry.Canonical.GrandSynthesis` weight=`2` dominant=`hypothesis_bridge` direction=`consumer`
- `InfoGeometry.Canonical.BerryPhase` weight=`2` dominant=`surrogate_or_vacuous` direction=`consumer`

## Exact Interfaces
### `InfoGeometry.Canonical.ConformalAlgebra`
- `mk` -> `ConformalInference` `[type]`
- `mk` -> `P` `[type]`
- `mk` -> `K` `[type]`
- `mk` -> `D` `[type]`
- `mk` -> `chiralScale` `[type]`
- `CI` -> `ConformalInference` `[type]`
- `D_def` -> `D` `[type]`
- `anomaly_breaks_weights` -> `P` `[type]`

### `InfoGeometry.Canonical.WeylTransportChiralBridge`
- `congr_simp` -> `ConformalInference` `[type,value]`
- `congr_simp` -> `chiralScale` `[type,value]`
- `FlatCurvatureChiralScaleBridge` -> `ConformalInference` `[type]`
- `mk` -> `ConformalInference` `[type]`
- `mk` -> `chiralScale` `[type]`
- `lineIntegrator` -> `ConformalInference` `[type,value]`
- `holonomyMap` -> `ConformalInference` `[type,value]`
- `flat_to_zeroCurvatureIntegral` -> `ConformalInference` `[type,value]`

### `InfoGeometry.Canonical.MasterSynthesis`
- `anomalyExclusion_package_of_chiralAnomaly_eq_zero` -> `ConformalInference` `[type,value]`
- `anomalyExclusion_package_of_chiralAnomaly_eq_zero` -> `spectralChiralProjector` `[type,value]`
- `anomalyExclusion_package_of_chiralAnomaly_eq_zero` -> `metricChiralProjector` `[type,value]`
- `anomalyExclusion_package_of_chiralAnomaly_eq_zero` -> `chiralAnomalyOperator` `[type,value]`
- `anomalyExclusion_package_of_chiralAnomaly_eq_zero` -> `projectors_commute_of_chiralAnomaly_eq_zero` `[value]`
- `anomalyExclusion_package_of_kahlerLogDet_unitRelativeVolume` -> `ConformalInference` `[type,value]`
- `anomalyExclusion_package_of_kahlerLogDet_unitRelativeVolume` -> `spectralChiralProjector` `[type,value]`
- `anomalyExclusion_package_of_kahlerLogDet_unitRelativeVolume` -> `metricChiralProjector` `[type,value]`

### `InfoGeometry.Canonical.ChiralCliffordBridge`
- `chiralGrading` -> `ConformalInference` `[type,value]`
- `chiralGrading` -> `toInverseKernel` `[value]`
- `generalizedChiralPlus` -> `ConformalInference` `[type,value]`
- `generalizedChiralPlus` -> `spectralChiralProjector` `[value]`
- `generalizedChiralMinus` -> `ConformalInference` `[type,value]`
- `generalizedChiralMinus` -> `spectralChiralProjector` `[value]`
- `chiralProjectorPlus` -> `ConformalInference` `[type,value]`
- `chiralProjectorMinus` -> `ConformalInference` `[type,value]`

### `InfoGeometry.Canonical.WeylInformationGauge`
- `chiralInferenceState_of_nonzero_anomaly` -> `ConformalInference` `[type,value]`
- `chiralInferenceState_of_nonzero_anomaly` -> `chiralAnomaly` `[value]`
- `chiralInferenceState_of_nonzero_anomaly` -> `chiralAnomalyOperator` `[type,value]`
- `chiralInferenceState_of_nonzero_anomaly` -> `epsilon` `[value]`
- `chiralInferenceState_of_nonzero_anomaly` -> `chiralScale` `[value]`
- `chiralInferenceState_of_nonzero_anomaly` -> `IsChiralInference` `[value]`
- `chiralInferenceState_of_nonzero_anomaly` -> `ChiralInferenceState` `[type,value]`
- `dilationAnomaly_sources_transportedEinsteinResidual` -> `ConformalInference` `[type,value]`

### `InfoGeometry.Canonical.AnomalyDilationBridge`
- `dilation_anomaly_jacobi_expansion` -> `ConformalInference` `[type,value]`
- `dilation_anomaly_jacobi_expansion` -> `D` `[type,value]`
- `dilation_anomaly_jacobi_expansion` -> `P_D` `[type,value]`
- `dilation_anomaly_jacobi_expansion` -> `P_MP` `[type,value]`
- `dilation_anomaly_jacobi_expansion` -> `chiralAnomalyOperator` `[type,value]`
- `trace_dilation_eq_zero` -> `ConformalInference` `[type,value]`
- `trace_dilation_eq_zero` -> `toInverseKernel` `[value]`
- `trace_dilation_eq_zero` -> `D` `[type,value]`

### `InfoGeometry.Canonical.ChiralTorsionBridge`
- `ChiralTorsionChentsovGibbsState` -> `ConformalInference` `[type,value]`
- `ChiralTorsionChentsovGibbsState` -> `IsChiralInference` `[value]`
- `chiralTorsionChentsovGibbsState_mk` -> `ConformalInference` `[type,value]`
- `chiralTorsionChentsovGibbsState_mk` -> `IsChiralInference` `[type,value]`
- `chiralTorsionChentsovGibbsState_of_twistedInference` -> `ConformalInference` `[type,value]`
- `chiralTorsionChentsovGibbsState_of_twistedInference` -> `IsChiralInference` `[value]`
- `torsion_nonzero_of_chiral` -> `ConformalInference` `[type,value]`
- `torsion_nonzero_of_chiral` -> `IsChiralInference` `[type,value]`

### `InfoGeometry.Canonical.ChiralAction`
- `chiralDirac` -> `ConformalInference` `[type,value]`
- `chiralDirac` -> `chiralAnomaly` `[value]`
- `chiralInformationAction` -> `ConformalInference` `[type,value]`
- `chiral_action_reduces_for_normal` -> `ConformalInference` `[type,value]`
- `chiral_action_reduces_for_normal` -> `chiralAnomaly` `[value]`
- `chiral_action_reduces_for_normal` -> `chiralScale` `[value]`
- `chiral_action_reduces_for_normal` -> `IsNormalInference` `[type,value]`

### `InfoGeometry.Canonical.CertifiedInverseKernel`
- `mk` -> `InverseKernel` `[type]`
- `toInverseKernel` -> `InverseKernel` `[type]`
- `mk` -> `A` `[type]`
- `mk` -> `A_D` `[type]`
- `mk` -> `A_MP` `[type]`
- `hDrazin` -> `A` `[type]`
- `hDrazin` -> `A_D` `[type]`
- `hMoorePenrose` -> `A` `[type]`

### `InfoGeometry.Canonical.GrandCanonicalExperts`
- `chiralScale_eq_zero_of_kahlerLogDet_unitRelativeVolume` -> `SinkhornMatrix` `[type,value]`
- `chiralScale_eq_zero_of_kahlerLogDet_unitRelativeVolume` -> `kahlerPotentialRN` `[type,value]`
- `chiralScale_eq_zero_of_kahlerLogDet_unitRelativeVolume` -> `relativeVolumeChangeRN` `[type,value]`
- `projectors_commute_of_kahlerLogDet_unitRelativeVolume` -> `SinkhornMatrix` `[type,value]`
- `projectors_commute_of_kahlerLogDet_unitRelativeVolume` -> `kahlerPotentialRN` `[type,value]`
- `projectors_commute_of_kahlerLogDet_unitRelativeVolume` -> `relativeVolumeChangeRN` `[type,value]`
- `logDetBarrier_selfConcordance_mechanics_of_kahlerLogDet_unitRelativeVolume` -> `SinkhornMatrix` `[type,value]`
- `logDetBarrier_selfConcordance_mechanics_of_kahlerLogDet_unitRelativeVolume` -> `kahlerPotentialRN` `[type,value]`

### `InfoGeometry.Canonical.Singular`
- `mk` -> `IsMoorePenroseInverse` `[type]`
- `mk` -> `IsDrazinInverse` `[type]`
- `hDrazin` -> `IsDrazinInverse` `[type]`
- `hMoorePenrose` -> `IsMoorePenroseInverse` `[type]`
- `einsteinAnomaly_eq_neg_rightChiralAnomaly` -> `EinsteinAnomaly` `[type,value]`
- `einsteinAnomaly_eq_neg_chiralAnomaly_of_projectorAgreement` -> `EinsteinAnomaly` `[type,value]`
- `spectralProjector_commutator_dilation_eq_neg_half_einstein_plus_chiral` -> `EinsteinAnomaly` `[type,value]`

### `InfoGeometry.Canonical.MoorePenrose`
- `dilation_eq_half_sub_mp_projectors` -> `rightProjector` `[type]`
- `dilation_eq_half_sub_mp_projectors` -> `leftProjector` `[type]`
- `P_MP` -> `leftProjector` `[value]`
- `P_MP_right` -> `rightProjector` `[value]`
- `einsteinAnomaly_eq_neg_rightChiralAnomaly` -> `rightProjector` `[value]`
- `einsteinAnomaly_eq_neg_chiralAnomaly_of_projectorAgreement` -> `rightProjector` `[type,value]`
- `einsteinAnomaly_eq_neg_chiralAnomaly_of_projectorAgreement` -> `leftProjector` `[type,value]`
- `spectralProjector_commutator_dilation_eq_half_sub_mp_projector_commutators` -> `rightProjector` `[type,value]`

### `InfoGeometry.Canonical.RicciMongeAmpere`
- `anomalyDrivenScalarRicciFlow_of_kahlerLogDet_normalized` -> `ScalarRicciFlow` `[type,value]`
- `anomalyDrivenScalarRicciFlow_of_kahlerLogDet_normalized` -> `SatisfiesNormalizedKaehlerRicciFlow` `[type,value]`
- `projectors_commute_of_kahlerLogDet_normalized_fixedpoint` -> `ScalarRicciFlow` `[type,value]`
- `projectors_commute_of_kahlerLogDet_normalized_fixedpoint` -> `scalarRicciBetaFunction` `[type,value]`
- `projectors_commute_of_kahlerLogDet_normalized_fixedpoint` -> `SatisfiesNormalizedKaehlerRicciFlow` `[type,value]`
- `einsteinEquation_of_projectorObstruction_source` -> `RicciTensor` `[type,value]`
- `einsteinEquation_of_projectorObstruction_source` -> `EinsteinEquationAt` `[type]`
- `einsteinEquation_of_projectorObstruction_source` -> `IsEinsteinKaehlerAtWith` `[type,value]`

### `InfoGeometry.Canonical.Drazin`
- `P_D` -> `projection` `[value]`
- `einsteinAnomaly_eq_neg_rightChiralAnomaly` -> `projection` `[value]`
- `einsteinAnomaly_eq_neg_chiralAnomaly_of_projectorAgreement` -> `projection` `[value]`

### `InfoGeometry.Canonical.ChiralEinsteinBridge`
- `anomalyDrivenScalarRicciFlow_of_kahlerLogDet_normalized` -> `SatisfiesAnomalyDrivenScalarRicciFlow` `[type]`
- `projectors_commute_of_kahlerLogDet_normalized_fixedpoint` -> `SatisfiesAnomalyDrivenScalarRicciFlow` `[value]`
- `einsteinEquation_of_projectorObstruction_source` -> `anomalyStressEnergyAt` `[type]`
- `einsteinEquation_of_projectorObstruction_source` -> `einsteinEquation_of_anomaly_source` `[value]`

### `InfoGeometry.Canonical.KaehlerGeometry`
- `einsteinEquation_of_projectorObstruction_source` -> `KaehlerInformationGeometry` `[type,value]`

### `InfoGeometry.Canonical.Rosetta`
- `sourceTension_eq_transportedEinsteinResidual` -> `chiralScale` `[type,value]`
- `rosetta_source_tension_three_presentations` -> `chiralAnomalyOperator` `[type,value]`
- `rosetta_source_tension_three_presentations` -> `chiralScale` `[type,value]`
- `modularCPT_source_rosetta` -> `chiralAnomalyOperator` `[type,value]`
- `modularCPT_source_rosetta` -> `chiralScale` `[type,value]`

### `InfoGeometry.Canonical.HolographicEmergence`
- `AnomalyScalePhase` -> `ConformalInference` `[type,value]`
- `AnomalyScalePhase` -> `ChiralInferenceState` `[value]`
- `anomalyScalePhase_of_nonzeroAnomaly` -> `ConformalInference` `[type,value]`
- `anomalyScalePhase_of_nonzeroAnomaly` -> `chiralAnomalyOperator` `[type,value]`

### `InfoGeometry.Canonical.GrandSynthesis`
- no direct declaration edges captured

### `InfoGeometry.Canonical.BerryPhase`
- `berryConnection` -> `ConformalInference` `[type,value]`
- `berryConnection` -> `chiralAnomaly` `[value]`

## Representative Seed Declarations
- `hDrazin` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/ConformalUnification.lean:44`
- `hMoorePenrose` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/ConformalUnification.lean:45`
- `spectralProjector_idempotent` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/ConformalUnification.lean:68`
- `mpRangeProjector_idempotent` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/ConformalUnification.lean:74`
- `metricProjector_idempotent` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/ConformalUnification.lean:80`
- `metricProjector_star` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/ConformalUnification.lean:86`
- `mpRangeProjector_star` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/ConformalUnification.lean:92`
- `specialConformal_eq_modularInversion_translation` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/ConformalUnification.lean:118`
- `translation_eq_modularInversion_specialConformal` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/ConformalUnification.lean:128`
- `dilation_eq_half_sub_mp_projectors` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/ConformalUnification.lean:153`
- `einsteinAnomaly_eq_neg_rightChiralAnomaly` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/ConformalUnification.lean:212`
- `einsteinAnomaly_eq_neg_chiralAnomaly_of_projectorAgreement` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/ConformalUnification.lean:222`
- `chiralScale_eq_projectorObstruction_norm` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/ConformalUnification.lean:244`
- `spectralProjector_commutator_dilation_eq_half_sub_mp_projector_commutators` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/ConformalUnification.lean:254`

## Neighbor Declarations
### `InfoGeometry.Canonical.ConformalAlgebra`
- `D_def` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/ConformalAlgebra.lean:30`
- `anomaly_breaks_weights` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/ConformalAlgebra.lean:32`
- `D_eq_CI_D` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/ConformalAlgebra.lean:40`
- `scale_anomaly_emergence` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/ConformalAlgebra.lean:83`
- `scale_anomaly_breaks_weight_closure` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/ConformalAlgebra.lean:93`
- `generatorCartanDecomposition_iff` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/ConformalAlgebra.lean:105`
- `generatorCartanDecomposition_of_parts` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/ConformalAlgebra.lean:114`
- `M_in_volumePreserving_of_cartan` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/ConformalAlgebra.lean:142`

### `InfoGeometry.Canonical.WeylTransportChiralBridge`
- `congr_simp` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/WeylTransportChiralBridge.lean:0`
- `flat_to_zeroCurvatureIntegral` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/WeylTransportChiralBridge.lean:26`
- `zeroCurvatureIntegral_to_chiralScale` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/WeylTransportChiralBridge.lean:30`
- `holonomy_eq_chiralScale_of_flat` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/WeylTransportChiralBridge.lean:36`
- `finiteSum_holonomy_eq_chiralScale_of_flat` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/WeylTransportChiralBridge.lean:79`
- `lineIntegrator` `neutral_definition` `def` at `lean/InfoGeometry/Canonical/WeylTransportChiralBridge.lean:24`
- `holonomyMap` `neutral_definition` `def` at `lean/InfoGeometry/Canonical/WeylTransportChiralBridge.lean:25`
- `finiteSumFlatCurvatureChiralScaleBridge` `neutral_definition` `def` at `lean/InfoGeometry/Canonical/WeylTransportChiralBridge.lean:51`

### `InfoGeometry.Canonical.MasterSynthesis`
- `anomalyExclusion_witness` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/MasterSynthesis.lean:79`
- `anomalyExclusion_package_of_chiralAnomaly_eq_zero` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/MasterSynthesis.lean:90`
- `anomalyExclusion_package_of_kahlerLogDet_unitRelativeVolume` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/MasterSynthesis.lean:104`
- `bridge_zpe_gravity` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/MasterSynthesis.lean:149`
- `bridge_fluid_helicity` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/MasterSynthesis.lean:165`
- `bits_to_gravity_to_fluid_capstone` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/MasterSynthesis.lean:181`
- `squeezingLogShear_bound_of_capstone_bekenstein_clause` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/MasterSynthesis.lean:261`
- `squeezingLogShear_bound_of_capstone_conjunction` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/MasterSynthesis.lean:278`

### `InfoGeometry.Canonical.ChiralCliffordBridge`
- `chiralGrading` `surrogate_or_vacuous` `def` at `lean/InfoGeometry/Canonical/ChiralCliffordBridge.lean:12`
- `anomaly_as_structure_constant` `package_reprojection` `theorem` at `lean/InfoGeometry/Canonical/ChiralCliffordBridge.lean:63`
- `cartan_collapse_of_normal` `package_reprojection` `theorem` at `lean/InfoGeometry/Canonical/ChiralCliffordBridge.lean:76`
- `generalizedChiralPlus` `package_reprojection` `def` at `lean/InfoGeometry/Canonical/ChiralCliffordBridge.lean:23`
- `generalizedChiralMinus` `package_reprojection` `def` at `lean/InfoGeometry/Canonical/ChiralCliffordBridge.lean:32`
- `chiralProjectorPlus` `package_reprojection` `def` at `lean/InfoGeometry/Canonical/ChiralCliffordBridge.lean:36`
- `chiralProjectorMinus` `package_reprojection` `def` at `lean/InfoGeometry/Canonical/ChiralCliffordBridge.lean:40`
- `IsCompactBeliefUpdate` `package_reprojection` `def` at `lean/InfoGeometry/Canonical/ChiralCliffordBridge.lean:46`

### `InfoGeometry.Canonical.WeylInformationGauge`
- `sinkhornTwoStep_eq_informationWeylGauge` `package_reprojection` `theorem` at `lean/InfoGeometry/Canonical/WeylInformationGauge.lean:32`
- `sinkhornGaugeFixing_is_marginal_closure` `package_reprojection` `theorem` at `lean/InfoGeometry/Canonical/WeylInformationGauge.lean:45`
- `weylOrderWitnessMatrix2_positiveRows` `package_reprojection` `theorem` at `lean/InfoGeometry/Canonical/WeylInformationGauge.lean:106`
- `weylOrderWitnessMatrix2_positiveCols` `package_reprojection` `theorem` at `lean/InfoGeometry/Canonical/WeylInformationGauge.lean:112`
- `weylOrderWitnessMatrix2_positiveCols_afterRow` `package_reprojection` `theorem` at `lean/InfoGeometry/Canonical/WeylInformationGauge.lean:118`
- `weylOrderWitnessMatrix2_positiveRows_afterCol` `package_reprojection` `theorem` at `lean/InfoGeometry/Canonical/WeylInformationGauge.lean:125`
- `weylOrderHysteresis_on_witnessMatrix2` `package_reprojection` `theorem` at `lean/InfoGeometry/Canonical/WeylInformationGauge.lean:132`
- `exists_updateOrderHysteresis_n2` `package_reprojection` `theorem` at `lean/InfoGeometry/Canonical/WeylInformationGauge.lean:149`

### `InfoGeometry.Canonical.AnomalyDilationBridge`
- `dilation_anomaly_jacobi_expansion` `package_reprojection` `theorem` at `lean/InfoGeometry/Canonical/AnomalyDilationBridge.lean:33`
- `trace_dilation_eq_zero` `package_reprojection` `theorem` at `lean/InfoGeometry/Canonical/AnomalyDilationBridge.lean:52`
- `normal_phase_of_trace_anomaly_in_finite_dim` `package_reprojection` `theorem` at `lean/InfoGeometry/Canonical/AnomalyDilationBridge.lean:70`

### `InfoGeometry.Canonical.ChiralTorsionBridge`
- `boltzmannRelativeVolumeEntropy_eq_divergence` `package_reprojection` `theorem` at `lean/InfoGeometry/Canonical/ChiralTorsionBridge.lean:48`
- `gibbsSmoothingOnGeneralizedKL_pos` `package_reprojection` `theorem` at `lean/InfoGeometry/Canonical/ChiralTorsionBridge.lean:66`
- `gibbsSmoothingOnGeneralizedKL_nonneg` `package_reprojection` `theorem` at `lean/InfoGeometry/Canonical/ChiralTorsionBridge.lean:73`
- `twistedInference_torsion_nonzero` `package_reprojection` `theorem` at `lean/InfoGeometry/Canonical/ChiralTorsionBridge.lean:152`
- `torsion_nonzero_of_chiral` `package_reprojection` `theorem` at `lean/InfoGeometry/Canonical/ChiralTorsionBridge.lean:158`
- `chentsov_and_gibbs_of_state` `package_reprojection` `theorem` at `lean/InfoGeometry/Canonical/ChiralTorsionBridge.lean:169`
- `torsion_nonzero_of_state_and_chiral` `package_reprojection` `theorem` at `lean/InfoGeometry/Canonical/ChiralTorsionBridge.lean:179`
- `relativeVacuumVolume` `package_reprojection` `def` at `lean/InfoGeometry/Canonical/ChiralTorsionBridge.lean:37`

### `InfoGeometry.Canonical.ChiralAction`
- `chiral_action_reduces_for_normal` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/ChiralAction.lean:33`
- `chiralDirac` `surrogate_or_vacuous` `def` at `lean/InfoGeometry/Canonical/ChiralAction.lean:12`
- `chiralInformationAction` `surrogate_or_vacuous` `def` at `lean/InfoGeometry/Canonical/ChiralAction.lean:21`

### `InfoGeometry.Canonical.CertifiedInverseKernel`
- `hDrazin` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean:36`
- `hMoorePenrose` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean:37`
- `spectralProjector_idempotent` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean:119`
- `mpRangeProjector_idempotent` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean:126`
- `metricProjector_idempotent` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean:133`
- `mpRangeProjector_star` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean:140`
- `metricProjector_star` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean:147`
- `A` `neutral_definition` `def` at `lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean:25`

### `InfoGeometry.Canonical.GrandCanonicalExperts`
- `ofNat_ctorIdx` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/GrandCanonicalExperts.lean:0`
- `ofNat_ctorIdx` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/GrandCanonicalExperts.lean:0`
- `congr_simp` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/GrandCanonicalExperts.lean:0`
- `congr_simp` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/GrandCanonicalExperts.lean:0`
- `gc_partition_eq_routerPartition` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/GrandCanonicalExperts.lean:25`
- `gc_gibbsWeight_eq_normalizedWeights` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/GrandCanonicalExperts.lean:29`
- `switchMatrix_apply` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/GrandCanonicalExperts.lean:45`
- `normalizedWeights_nonneg` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/GrandCanonicalExperts.lean:49`

### `InfoGeometry.Canonical.Singular`
- `EinsteinAnomaly_eq_zero_of_regularization_pair` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/Singular.lean:197`
- `EinsteinAnomaly_eq_zero_of_selfAdjoint_idempotent` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/Singular.lean:205`
- `exists_drazinInverse_global` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/Singular.lean:245`
- `exists_moorePenroseInverse_global` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/Singular.lean:286`
- `IsMoorePenroseInverse` `neutral_definition` `def` at `lean/InfoGeometry/Canonical/Singular.lean:27`
- `IsDrazinInverse` `neutral_definition` `def` at `lean/InfoGeometry/Canonical/Singular.lean:31`
- `EinsteinAnomaly` `neutral_definition` `def` at `lean/InfoGeometry/Canonical/Singular.lean:35`
- `exists_regularization_pair_of_selfAdjoint_idempotent` `package_reprojection` `theorem` at `lean/InfoGeometry/Canonical/Singular.lean:145`

### `InfoGeometry.Canonical.MoorePenrose`
- `mk` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/MoorePenrose.lean:34`
- `aba_eq_a` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/MoorePenrose.lean:43`
- `bab_eq_b` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/MoorePenrose.lean:46`
- `ab_star` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/MoorePenrose.lean:49`
- `ba_star` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/MoorePenrose.lean:52`
- `rightProjector_idempotent` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/MoorePenrose.lean:61`
- `rightProjector_star` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/MoorePenrose.lean:71`
- `leftProjector_idempotent` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/MoorePenrose.lean:76`

### `InfoGeometry.Canonical.RicciMongeAmpere`
- `scalarCurvatureOnFrame_eq_einstein_multiple` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/RicciMongeAmpere.lean:46`
- `metricLogDet_differentiable` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/RicciMongeAmpere.lean:106`
- `metricLogDet_fderiv_apply_differentiable` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/RicciMongeAmpere.lean:113`
- `metricLogDet_fderiv_apply_differentiableAt` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/RicciMongeAmpere.lean:120`
- `nonneg` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/RicciMongeAmpere.lean:137`
- `ricci_eq_metric` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/RicciMongeAmpere.lean:138`
- `ricci_component_invariant_at_fixed_point` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/RicciMongeAmpere.lean:174`
- `ricci_tensor_invariant_at_fixed_point` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/RicciMongeAmpere.lean:191`

### `InfoGeometry.Canonical.Drazin`
- `mk` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/Drazin.lean:15`
- `comm` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/Drazin.lean:23`
- `idempotent` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/Drazin.lean:26`
- `power` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/Drazin.lean:29`
- `projection_is_idempotent` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/Drazin.lean:38`
- `complementaryProjection_is_idempotent` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/Drazin.lean:44`
- `projection_mul_complementaryProjection` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/Drazin.lean:53`
- `complementaryProjection_mul_projection` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/Drazin.lean:61`

### `InfoGeometry.Canonical.ChiralEinsteinBridge`
- `anomalyStressEnergyAt_apply` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/ChiralEinsteinBridge.lean:29`
- `anomalyStressEnergyAt_zero` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/ChiralEinsteinBridge.lean:33`
- `einsteinEquation_of_anomaly_source` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/ChiralEinsteinBridge.lean:39`
- `exists_einsteinEquation_of_bistochastic_routingAnomaly` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/ChiralEinsteinBridge.lean:64`
- `anomalyDriven_zeroSource_iff_normalized` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/ChiralEinsteinBridge.lean:103`
- `anomalyDriven_fixedpoint_tracks_source` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/ChiralEinsteinBridge.lean:110`
- `anomalyDrivenScalarRicci_fixedpoint_tracks_source` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/ChiralEinsteinBridge.lean:132`
- `anomalyDriven_fixedpoint_eq_inverseEpsilon` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/ChiralEinsteinBridge.lean:149`

### `InfoGeometry.Canonical.KaehlerGeometry`
- `j_sq_eq_neg_id` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/KaehlerGeometry.lean:30`
- `compatibility` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/KaehlerGeometry.lean:32`
- `logF_eq_potential` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/KaehlerGeometry.lean:46`
- `logF_apply` `likely_constructive` `theorem` at `lean/InfoGeometry/Canonical/KaehlerGeometry.lean:49`
- `SymplecticForm` `neutral_definition` `def` at `lean/InfoGeometry/Canonical/KaehlerGeometry.lean:12`
- `H` `neutral_definition` `def` at `lean/InfoGeometry/Canonical/KaehlerGeometry.lean:26`
- `ω` `neutral_definition` `def` at `lean/InfoGeometry/Canonical/KaehlerGeometry.lean:27`
- `J` `neutral_definition` `def` at `lean/InfoGeometry/Canonical/KaehlerGeometry.lean:28`

### `InfoGeometry.Canonical.Rosetta`
- `instCompleteSpaceVCl11DoubledCore` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/Rosetta.lean:430`
- `modularComplexI_toLinearMap_eq_realMajoranaKAxis` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/Rosetta.lean:434`
- `sourceTension_eq_transportedEinsteinResidual` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/Rosetta.lean:443`
- `transportedEinsteinResidual_eq_einsteinInducedChemicalPotential` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/Rosetta.lean:462`
- `einsteinInducedChemicalPotential_lift_eq_einsteinFockDeformationOperator` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/Rosetta.lean:477`
- `modularAnomalyGenerator_eq_commutator_of_transport_source` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/Rosetta.lean:492`
- `rosetta_source_tension_three_presentations` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/Rosetta.lean:507`
- `modularCPT_source_rosetta` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/Rosetta.lean:564`

### `InfoGeometry.Canonical.HolographicEmergence`
- `emergentTimeFlow_of_sinkhornTrajectory` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/HolographicEmergence.lean:39`
- `anomalyScalePhase_of_nonzeroAnomaly` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/HolographicEmergence.lean:57`
- `pathDependence_of_twistedInference` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/HolographicEmergence.lean:71`
- `exists_gaugeOrderHysteresis_witness` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/HolographicEmergence.lean:77`
- `EmergentTimeFlow` `surrogate_or_vacuous` `def` at `lean/InfoGeometry/Canonical/HolographicEmergence.lean:35`
- `AnomalyScalePhase` `surrogate_or_vacuous` `def` at `lean/InfoGeometry/Canonical/HolographicEmergence.lean:53`

### `InfoGeometry.Canonical.GrandSynthesis`
- `log_mongeAmpereDensity_eq_logAbsDet_metricOp` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/GrandSynthesis.lean:230`
- `thermodynamicEquilibrium_of_doublyStochastic` `package_reprojection` `theorem` at `lean/InfoGeometry/Canonical/GrandSynthesis.lean:51`
- `ricci_component_constant_of_geometricEquilibrium` `package_reprojection` `theorem` at `lean/InfoGeometry/Canonical/GrandSynthesis.lean:71`
- `relativeTomitaTakesakiOp_apply` `package_reprojection` `theorem` at `lean/InfoGeometry/Canonical/GrandSynthesis.lean:116`
- `relativeCountDensity_eq_rn_lift` `package_reprojection` `theorem` at `lean/InfoGeometry/Canonical/GrandSynthesis.lean:121`
- `relativeLogDensityMean_mul` `package_reprojection` `theorem` at `lean/InfoGeometry/Canonical/GrandSynthesis.lean:126`
- `logAbsDetMatrix_mul` `package_reprojection` `theorem` at `lean/InfoGeometry/Canonical/GrandSynthesis.lean:155`
- `logAbsDetMatrix_kronecker` `package_reprojection` `theorem` at `lean/InfoGeometry/Canonical/GrandSynthesis.lean:171`

### `InfoGeometry.Canonical.BerryPhase`
- `berryPhase_eq_anomaly_flux` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/BerryPhase.lean:46`
- `informationBerryPhase_eq_loopLength_mul_chiralAnomalyIndex` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/BerryPhase.lean:53`
- `informationBerryPhase_eq_loopLength_mul_epsilon_mul_rank` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/BerryPhase.lean:60`
- `informationBerryPhase_ne_zero_of_loopLength_ne_zero_of_chiralAnomalyIndex_ne_zero` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/BerryPhase.lean:72`
- `berryPhase_ne_zero_of_anomaly_flux_ne_zero` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/BerryPhase.lean:83`
- `berry_phase_vanishes_for_normal` `surrogate_or_vacuous` `theorem` at `lean/InfoGeometry/Canonical/BerryPhase.lean:93`
- `berryConnection` `surrogate_or_vacuous` `def` at `lean/InfoGeometry/Canonical/BerryPhase.lean:20`
- `informationBerryPhase` `surrogate_or_vacuous` `def` at `lean/InfoGeometry/Canonical/BerryPhase.lean:30`

## Prompt Packet

```text
You are helping close a local Lean 4 theorem frontier.

Hard constraints:
- Do not invent nonexistent theorems, defs, or imports.
- Do not claim a proof exists unless it is directly implied by the context below.
- Stay close to the current codebase vocabulary and theorem names.
- Output candidate bridge statements and proof attack plans only.
- Prefer Lean-style theorem signatures over prose.
- Treat the support cone as constructive substrate and the consumer cone as obligations to discharge.

Goal:
Propose 3-5 small bridge statements that replace surrogate surfaces inside `InfoGeometry.Canonical.ConformalUnification` by using the exact support cone and reverse consumer cone below.

Seed pressure:
- burn-down rank 1, score 2607.829, dominant pressure surrogate_or_vacuous
- mix (hypothesis/package/surrogate): 0/0/96

Support cone modules:
- InfoGeometry.Canonical.CertifiedInverseKernel (edge weight 83, dominant likely_constructive)
- InfoGeometry.Canonical.GrandCanonicalExperts (edge weight 24, dominant likely_constructive)
- InfoGeometry.Canonical.Singular (edge weight 23, dominant likely_constructive)
- InfoGeometry.Canonical.MoorePenrose (edge weight 16, dominant likely_constructive)
- InfoGeometry.Canonical.RicciMongeAmpere (edge weight 11, dominant likely_constructive)
- InfoGeometry.Canonical.Drazin (edge weight 4, dominant likely_constructive)
- InfoGeometry.Canonical.ChiralEinsteinBridge (edge weight 4, dominant likely_constructive)
- InfoGeometry.Canonical.KaehlerGeometry (edge weight 1, dominant likely_constructive)

Reverse consumer modules:
- InfoGeometry.Canonical.ConformalAlgebra (edge weight 64, dominant surrogate_or_vacuous)
- InfoGeometry.Canonical.WeylTransportChiralBridge (edge weight 33, dominant likely_constructive)
- InfoGeometry.Canonical.MasterSynthesis (edge weight 23, dominant surrogate_or_vacuous)
- InfoGeometry.Canonical.ChiralCliffordBridge (edge weight 20, dominant package_reprojection)
- InfoGeometry.Canonical.WeylInformationGauge (edge weight 17, dominant hypothesis_bridge)
- InfoGeometry.Canonical.AnomalyDilationBridge (edge weight 14, dominant package_reprojection)
- InfoGeometry.Canonical.ChiralTorsionBridge (edge weight 12, dominant package_reprojection)
- InfoGeometry.Canonical.ChiralAction (edge weight 7, dominant surrogate_or_vacuous)

Exact seed interfaces:
- InfoGeometry.Canonical.ConformalAlgebra:
  - mk -> ConformalInference [type]
  - mk -> P [type]
  - mk -> K [type]
  - mk -> D [type]
  - mk -> chiralScale [type]
  - CI -> ConformalInference [type]
  - D_def -> D [type]
  - anomaly_breaks_weights -> P [type]
- InfoGeometry.Canonical.WeylTransportChiralBridge:
  - congr_simp -> ConformalInference [type,value]
  - congr_simp -> chiralScale [type,value]
  - FlatCurvatureChiralScaleBridge -> ConformalInference [type]
  - mk -> ConformalInference [type]
  - mk -> chiralScale [type]
  - lineIntegrator -> ConformalInference [type,value]
  - holonomyMap -> ConformalInference [type,value]
  - flat_to_zeroCurvatureIntegral -> ConformalInference [type,value]
- InfoGeometry.Canonical.MasterSynthesis:
  - anomalyExclusion_package_of_chiralAnomaly_eq_zero -> ConformalInference [type,value]
  - anomalyExclusion_package_of_chiralAnomaly_eq_zero -> spectralChiralProjector [type,value]
  - anomalyExclusion_package_of_chiralAnomaly_eq_zero -> metricChiralProjector [type,value]
  - anomalyExclusion_package_of_chiralAnomaly_eq_zero -> chiralAnomalyOperator [type,value]
  - anomalyExclusion_package_of_chiralAnomaly_eq_zero -> projectors_commute_of_chiralAnomaly_eq_zero [value]
  - anomalyExclusion_package_of_kahlerLogDet_unitRelativeVolume -> ConformalInference [type,value]
  - anomalyExclusion_package_of_kahlerLogDet_unitRelativeVolume -> spectralChiralProjector [type,value]
  - anomalyExclusion_package_of_kahlerLogDet_unitRelativeVolume -> metricChiralProjector [type,value]
- InfoGeometry.Canonical.ChiralCliffordBridge:
  - chiralGrading -> ConformalInference [type,value]
  - chiralGrading -> toInverseKernel [value]
  - generalizedChiralPlus -> ConformalInference [type,value]
  - generalizedChiralPlus -> spectralChiralProjector [value]
  - generalizedChiralMinus -> ConformalInference [type,value]
  - generalizedChiralMinus -> spectralChiralProjector [value]
  - chiralProjectorPlus -> ConformalInference [type,value]
  - chiralProjectorMinus -> ConformalInference [type,value]
- InfoGeometry.Canonical.WeylInformationGauge:
  - chiralInferenceState_of_nonzero_anomaly -> ConformalInference [type,value]
  - chiralInferenceState_of_nonzero_anomaly -> chiralAnomaly [value]
  - chiralInferenceState_of_nonzero_anomaly -> chiralAnomalyOperator [type,value]
  - chiralInferenceState_of_nonzero_anomaly -> epsilon [value]
  - chiralInferenceState_of_nonzero_anomaly -> chiralScale [value]
  - chiralInferenceState_of_nonzero_anomaly -> IsChiralInference [value]
  - chiralInferenceState_of_nonzero_anomaly -> ChiralInferenceState [type,value]
  - dilationAnomaly_sources_transportedEinsteinResidual -> ConformalInference [type,value]
- InfoGeometry.Canonical.AnomalyDilationBridge:
  - dilation_anomaly_jacobi_expansion -> ConformalInference [type,value]
  - dilation_anomaly_jacobi_expansion -> D [type,value]
  - dilation_anomaly_jacobi_expansion -> P_D [type,value]
  - dilation_anomaly_jacobi_expansion -> P_MP [type,value]
  - dilation_anomaly_jacobi_expansion -> chiralAnomalyOperator [type,value]
  - trace_dilation_eq_zero -> ConformalInference [type,value]
  - trace_dilation_eq_zero -> toInverseKernel [value]
  - trace_dilation_eq_zero -> D [type,value]
- InfoGeometry.Canonical.ChiralTorsionBridge:
  - ChiralTorsionChentsovGibbsState -> ConformalInference [type,value]
  - ChiralTorsionChentsovGibbsState -> IsChiralInference [value]
  - chiralTorsionChentsovGibbsState_mk -> ConformalInference [type,value]
  - chiralTorsionChentsovGibbsState_mk -> IsChiralInference [type,value]
  - chiralTorsionChentsovGibbsState_of_twistedInference -> ConformalInference [type,value]
  - chiralTorsionChentsovGibbsState_of_twistedInference -> IsChiralInference [value]
  - torsion_nonzero_of_chiral -> ConformalInference [type,value]
  - torsion_nonzero_of_chiral -> IsChiralInference [type,value]
- InfoGeometry.Canonical.ChiralAction:
  - chiralDirac -> ConformalInference [type,value]
  - chiralDirac -> chiralAnomaly [value]
  - chiralInformationAction -> ConformalInference [type,value]
  - chiral_action_reduces_for_normal -> ConformalInference [type,value]
  - chiral_action_reduces_for_normal -> chiralAnomaly [value]
  - chiral_action_reduces_for_normal -> chiralScale [value]
  - chiral_action_reduces_for_normal -> IsNormalInference [type,value]
- InfoGeometry.Canonical.CertifiedInverseKernel:
  - mk -> InverseKernel [type]
  - toInverseKernel -> InverseKernel [type]
  - mk -> A [type]
  - mk -> A_D [type]
  - mk -> A_MP [type]
  - hDrazin -> A [type]
  - hDrazin -> A_D [type]
  - hMoorePenrose -> A [type]
- InfoGeometry.Canonical.GrandCanonicalExperts:
  - chiralScale_eq_zero_of_kahlerLogDet_unitRelativeVolume -> SinkhornMatrix [type,value]
  - chiralScale_eq_zero_of_kahlerLogDet_unitRelativeVolume -> kahlerPotentialRN [type,value]
  - chiralScale_eq_zero_of_kahlerLogDet_unitRelativeVolume -> relativeVolumeChangeRN [type,value]
  - projectors_commute_of_kahlerLogDet_unitRelativeVolume -> SinkhornMatrix [type,value]
  - projectors_commute_of_kahlerLogDet_unitRelativeVolume -> kahlerPotentialRN [type,value]
  - projectors_commute_of_kahlerLogDet_unitRelativeVolume -> relativeVolumeChangeRN [type,value]
  - logDetBarrier_selfConcordance_mechanics_of_kahlerLogDet_unitRelativeVolume -> SinkhornMatrix [type,value]
  - logDetBarrier_selfConcordance_mechanics_of_kahlerLogDet_unitRelativeVolume -> kahlerPotentialRN [type,value]
- InfoGeometry.Canonical.Singular:
  - mk -> IsMoorePenroseInverse [type]
  - mk -> IsDrazinInverse [type]
  - hDrazin -> IsDrazinInverse [type]
  - hMoorePenrose -> IsMoorePenroseInverse [type]
  - einsteinAnomaly_eq_neg_rightChiralAnomaly -> EinsteinAnomaly [type,value]
  - einsteinAnomaly_eq_neg_chiralAnomaly_of_projectorAgreement -> EinsteinAnomaly [type,value]
  - spectralProjector_commutator_dilation_eq_neg_half_einstein_plus_chiral -> EinsteinAnomaly [type,value]
- InfoGeometry.Canonical.MoorePenrose:
  - dilation_eq_half_sub_mp_projectors -> rightProjector [type]
  - dilation_eq_half_sub_mp_projectors -> leftProjector [type]
  - P_MP -> leftProjector [value]
  - P_MP_right -> rightProjector [value]
  - einsteinAnomaly_eq_neg_rightChiralAnomaly -> rightProjector [value]
  - einsteinAnomaly_eq_neg_chiralAnomaly_of_projectorAgreement -> rightProjector [type,value]
  - einsteinAnomaly_eq_neg_chiralAnomaly_of_projectorAgreement -> leftProjector [type,value]
  - spectralProjector_commutator_dilation_eq_half_sub_mp_projector_commutators -> rightProjector [type,value]
- InfoGeometry.Canonical.RicciMongeAmpere:
  - anomalyDrivenScalarRicciFlow_of_kahlerLogDet_normalized -> ScalarRicciFlow [type,value]
  - anomalyDrivenScalarRicciFlow_of_kahlerLogDet_normalized -> SatisfiesNormalizedKaehlerRicciFlow [type,value]
  - projectors_commute_of_kahlerLogDet_normalized_fixedpoint -> ScalarRicciFlow [type,value]
  - projectors_commute_of_kahlerLogDet_normalized_fixedpoint -> scalarRicciBetaFunction [type,value]
  - projectors_commute_of_kahlerLogDet_normalized_fixedpoint -> SatisfiesNormalizedKaehlerRicciFlow [type,value]
  - einsteinEquation_of_projectorObstruction_source -> RicciTensor [type,value]
  - einsteinEquation_of_projectorObstruction_source -> EinsteinEquationAt [type]
  - einsteinEquation_of_projectorObstruction_source -> IsEinsteinKaehlerAtWith [type,value]
- InfoGeometry.Canonical.Drazin:
  - P_D -> projection [value]
  - einsteinAnomaly_eq_neg_rightChiralAnomaly -> projection [value]
  - einsteinAnomaly_eq_neg_chiralAnomaly_of_projectorAgreement -> projection [value]
- InfoGeometry.Canonical.ChiralEinsteinBridge:
  - anomalyDrivenScalarRicciFlow_of_kahlerLogDet_normalized -> SatisfiesAnomalyDrivenScalarRicciFlow [type]
  - projectors_commute_of_kahlerLogDet_normalized_fixedpoint -> SatisfiesAnomalyDrivenScalarRicciFlow [value]
  - einsteinEquation_of_projectorObstruction_source -> anomalyStressEnergyAt [type]
  - einsteinEquation_of_projectorObstruction_source -> einsteinEquation_of_anomaly_source [value]
- InfoGeometry.Canonical.KaehlerGeometry:
  - einsteinEquation_of_projectorObstruction_source -> KaehlerInformationGeometry [type,value]
- InfoGeometry.Canonical.Rosetta:
  - sourceTension_eq_transportedEinsteinResidual -> chiralScale [type,value]
  - rosetta_source_tension_three_presentations -> chiralAnomalyOperator [type,value]
  - rosetta_source_tension_three_presentations -> chiralScale [type,value]
  - modularCPT_source_rosetta -> chiralAnomalyOperator [type,value]
  - modularCPT_source_rosetta -> chiralScale [type,value]
- InfoGeometry.Canonical.HolographicEmergence:
  - AnomalyScalePhase -> ConformalInference [type,value]
  - AnomalyScalePhase -> ChiralInferenceState [value]
  - anomalyScalePhase_of_nonzeroAnomaly -> ConformalInference [type,value]
  - anomalyScalePhase_of_nonzeroAnomaly -> chiralAnomalyOperator [type,value]
- InfoGeometry.Canonical.GrandSynthesis:
- InfoGeometry.Canonical.BerryPhase:
  - berryConnection -> ConformalInference [type,value]
  - berryConnection -> chiralAnomaly [value]

Representative seed declarations:
- InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.hDrazin (surrogate_or_vacuous, theorem)
- InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.hMoorePenrose (surrogate_or_vacuous, theorem)
- InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.spectralProjector_idempotent (surrogate_or_vacuous, theorem)
- InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.mpRangeProjector_idempotent (surrogate_or_vacuous, theorem)
- InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.metricProjector_idempotent (surrogate_or_vacuous, theorem)
- InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.metricProjector_star (surrogate_or_vacuous, theorem)
- InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference.mpRangeProjector_star (surrogate_or_vacuous, theorem)
- InfoGeometry.Canonical.ConformalUnification.ConformalInference.specialConformal_eq_modularInversion_translation (surrogate_or_vacuous, theorem)
- InfoGeometry.Canonical.ConformalUnification.ConformalInference.translation_eq_modularInversion_specialConformal (surrogate_or_vacuous, theorem)
- InfoGeometry.Canonical.ConformalUnification.ConformalInference.dilation_eq_half_sub_mp_projectors (surrogate_or_vacuous, theorem)
- InfoGeometry.Canonical.ConformalUnification.ConformalInference.einsteinAnomaly_eq_neg_rightChiralAnomaly (surrogate_or_vacuous, theorem)
- InfoGeometry.Canonical.ConformalUnification.ConformalInference.einsteinAnomaly_eq_neg_chiralAnomaly_of_projectorAgreement (surrogate_or_vacuous, theorem)
- InfoGeometry.Canonical.ConformalUnification.ConformalInference.chiralScale_eq_projectorObstruction_norm (surrogate_or_vacuous, theorem)
- InfoGeometry.Canonical.ConformalUnification.ConformalInference.spectralProjector_commutator_dilation_eq_half_sub_mp_projector_commutators (surrogate_or_vacuous, theorem)

Task:
For each candidate, provide exactly:
1. name
2. Lean-style signature sketch
3. which exact interface edge or module relation it closes
4. likely proof ingredients already present in the support cone
5. risk level (low / medium / high)

Strong preference:
- use constructive support modules before introducing any new abstractions
- target declarations that would reduce surrogate load in the seed module
- expose obligations needed by reverse consumers instead of inventing capstones

Do not output proof scripts.
Do not output more than 5 candidates.
```

