# L0/L1 proof-root audit

Scope: live source scan of `lean/**/*.lean` for `@[rep_depth count]` / `@[rep_depth projective]`, plus comparison with existing derived DAG artifact. Lean source/build remains authority; DAG artifact is supporting/staleness-prone evidence.

- source tagged declarations found by local scan: `119`
- source L0/count tagged declarations: `5`
- source L1/projective tagged declarations: `114`
- source Prop/theorem/lemma candidates: `67`
- source Prop candidates with Nonempty/Exists/Witness/Interface signals: `23`
- standalone live `axiom`/`opaque`/`sorry`/`admit` candidates after comment/string strip: `0` actual proof placeholders; `1` syntax-name false positive
- derived artifact comparison: loaded `artifacts/dag/representation-depth-tags.json`: 217 L0/L1 rows; Counter({1: 215, 0: 2}); kinds Counter({'theorem': 153, 'def': 63, 'inductive': 1})

## Source summary by depth/kind/prop-candidate

- `('count', 'def', False)`: `2`
- `('count', 'structure', True)`: `1`
- `('count', 'theorem', True)`: `2`
- `('projective', 'abbrev', False)`: `4`
- `('projective', 'def', False)`: `45`
- `('projective', 'def', True)`: `15`
- `('projective', 'structure', False)`: `1`
- `('projective', 'structure', True)`: `2`
- `('projective', 'theorem', True)`: `47`

## Standalone cheat-token candidates

- no actual standalone proof-placeholder candidate found
- false positive: `lean/InfoGeometry/Meta/StrictDef.lean:18` names the syntax node ``Lean.Parser.Term.«sorry»`` inside the strict-declaration checker; it is not a proof placeholder

## L0/L1 Prop candidates with packaging/interface/witness signals

- `lean/InfoGeometry/GromovWittenErlangen/GWCanonicalCountRayBridge.lean:45` `projective` `structure GWCanonicalCountRayBridge` signals=['Nonempty', 'Witness']
- `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean:406` `projective` `theorem gaugeSectionFinProb_countRay_apply_toReal` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean:753` `projective` `theorem relativeModularHamiltonian_sub_countMassShift_cocycle` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean:38` `projective` `theorem RestrictedRelativeModularData.local_projectiveLogGenerator_eq_local_modularPotential_ae` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean:68` `projective` `theorem RestrictedRelativeModularData.local_projectiveLogGenerator_eq_local_modularPotential` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean:93` `projective` `theorem RestrictedRelativeModularData.local_projectiveLogGenerator_eq_pullback_ambient_add_shift_ae` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean:117` `projective` `theorem RestrictedRelativeModularData.local_projectiveLogGenerator_eq_pullback_ambient_add_shift` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean:144` `projective` `theorem RestrictedRelativeModularData.local_modularPotential_eq_projectiveCountHamiltonianProfile_of_countRays` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean:167` `projective` `theorem RestrictedRelativeModularData.projectiveCountHamiltonianProfile_eq_pullback_ambient_add_shift` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/ModularKLDivergenceBridge.lean:43` `projective` `theorem generalizedKL_scale_shape_split` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/ModularKLDivergenceBridge.lean:59` `projective` `theorem generalizedKL_eq_klLike_add_massSlack` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/ModularKLDivergenceBridge.lean:72` `projective` `theorem generalizedKL_scale_shape_terms_nonneg` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/ModularKLDivergenceBridge.lean:99` `projective` `theorem generalizedKL_scale_shape_mass_term_pos_of_mass_ne` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/ModularKLDivergenceBridge.lean:116` `projective` `theorem generalizedKL_scale_shape_split_with_nonneg` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/RelativeModularRecomposition.lean:156` `projective` `def PolarizedRecompositionData.exactPotentialRecomposition` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/OddDefectFunctional.lean:49` `projective` `theorem projectiveCountDefectFunctional_eq_countMassShift` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/OddDefectFunctional.lean:61` `projective` `theorem projectiveCountDefectFunctional_eq_neg_log_relativeVolumeChange` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/OddDefectFunctional.lean:83` `projective` `theorem projectiveCountDefectBarrier_nonneg` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/ModularSurprisalThermoPacket.lean:49` `projective` `theorem representativeModularPotential_eq_negative_relativeLogDensity` signals=['Nonempty', 'Interface']
- `lean/InfoGeometry/Canonical/ModularSurprisalThermoPacket.lean:60` `projective` `theorem relativeModularPotential_eq_negative_relativeLogDensity` signals=['Nonempty', 'Interface']
- `lean/InfoGeometry/Canonical/RNDeterminantConnesChainBridge.lean:37` `projective` `theorem relativeDensity_state_chain` signals=['Interface']
- `lean/InfoGeometry/Canonical/RNDeterminantConnesChainBridge.lean:85` `projective` `theorem rn_state_chain` signals=['Interface']
- `lean/InfoGeometry/Canonical/FirstQuantizationProbability.lean:69` `projective` `theorem classicalSurprisal_eq_relativeModularPotential` signals=['Nonempty']

## Source L0 declarations found

- `lean/InfoGeometry/GromovWittenErlangen/ProjectiveCountDrazinFrobeniusBridge.lean:97` `theorem countShadow_holds` prop=True signals=[]
- `lean/InfoGeometry/GromovWittenErlangen/GWProjectiveCountCalibration.lean:44` `structure GWProjectiveCountCalibration` prop=True signals=[]
- `lean/InfoGeometry/GromovWittenErlangen/GWProjectiveCountCalibration.lean:90` `theorem countShadow_holds` prop=True signals=[]
- `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean:44` `def relativeCountLogDensity` prop=False signals=[]
- `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean:50` `def relativeCountModularProfile` prop=False signals=[]

## All source L0/L1 Prop candidates

- `lean/InfoGeometry/GromovWittenErlangen/ProjectiveCountDrazinFrobeniusBridge.lean:35` `projective` `structure ProjectiveCountDrazinFrobeniusBridge` signals=[]
- `lean/InfoGeometry/GromovWittenErlangen/ProjectiveCountDrazinFrobeniusBridge.lean:97` `count` `theorem countShadow_holds` signals=[]
- `lean/InfoGeometry/GromovWittenErlangen/ProjectiveCountDrazinFrobeniusBridge.lean:103` `projective` `theorem localization_packet_matches_projectiveCounts` signals=[]
- `lean/InfoGeometry/GromovWittenErlangen/ProjectiveCountDrazinFrobeniusBridge.lean:148` `projective` `theorem normalizedShape_scale_counts` signals=[]
- `lean/InfoGeometry/GromovWittenErlangen/GWProjectiveCountCalibration.lean:44` `count` `structure GWProjectiveCountCalibration` signals=[]
- `lean/InfoGeometry/GromovWittenErlangen/GWProjectiveCountCalibration.lean:90` `count` `theorem countShadow_holds` signals=[]
- `lean/InfoGeometry/GromovWittenErlangen/GWProjectiveCountCalibration.lean:109` `projective` `theorem normalizedShape_scale_counts` signals=[]
- `lean/InfoGeometry/GromovWittenErlangen/GWProjectiveCountCalibration.lean:120` `projective` `theorem normalizedShape_eq_of_samePositiveRay` signals=[]
- `lean/InfoGeometry/GromovWittenErlangen/GWProjectiveCountCalibration.lean:131` `projective` `theorem normalizedShape_sum_eq_one` signals=[]
- `lean/InfoGeometry/GromovWittenErlangen/GWProjectiveCountCalibration.lean:142` `projective` `theorem finiteArithmeticWeight_eq_partition_mul_normalizedShape` signals=[]
- `lean/InfoGeometry/GromovWittenErlangen/GWCanonicalCountRayBridge.lean:45` `projective` `structure GWCanonicalCountRayBridge` signals=['Nonempty', 'Witness']
- `lean/InfoGeometry/GromovWittenErlangen/GWCanonicalCountRayBridge.lean:189` `projective` `theorem projectiveHamiltonianProfile_eq_relativeModularPotential` signals=[]
- `lean/InfoGeometry/Canonical/TwistorHodgePalatialBridge.lean:230` `projective` `theorem hodgeStarSelfDualSplitOfIncidentNullSeparation_selfDualCondition` signals=[]
- `lean/InfoGeometry/Canonical/TwistorHodgePalatialBridge.lean:238` `projective` `theorem hodgeStarSelfDualSplitOfIncidentNullSeparation_antiSelfDualCondition` signals=[]
- `lean/InfoGeometry/Canonical/TwistorHodgePalatialBridge.lean:246` `projective` `theorem hodgeStarSelfDualSplitOfIncidentNullSeparation_incidenceCompatible` signals=[]
- `lean/InfoGeometry/Canonical/RelativePotentialCore.lean:358` `projective` `theorem relativeModularPotential_eq_logDensity_base_sub_logDensity` signals=[]
- `lean/InfoGeometry/Canonical/GrandCanonicalGaussianScaleShape.lean:109` `projective` `theorem generalizedKL_eq_ISShape_add_scaleTerm` signals=[]
- `lean/InfoGeometry/Canonical/GrandCanonicalGaussianScaleShape.lean:122` `projective` `theorem generalizedKL_unnormalizedGrandCanonicalGaussian_eq_ISShape_add_scaleTerm` signals=[]
- `lean/InfoGeometry/Canonical/MajoranaKreinCartanSplit.lean:47` `projective` `theorem projectiveDynamics_J_eq_projectiveMap_tomitaAtomSeed_J` signals=[]
- `lean/InfoGeometry/Canonical/MajoranaKreinCartanSplit.lean:53` `projective` `theorem projectiveDynamics_epsilon_eq_projectiveMap_tomitaAtomSeed_eps` signals=[]
- `lean/InfoGeometry/Canonical/MajoranaKreinCartanSplit.lean:59` `projective` `theorem projectiveDynamics_I_eq_projectiveMap_tomitaAtomSeed_phaseAxis` signals=[]
- `lean/InfoGeometry/Canonical/MajoranaKreinCartanSplit.lean:65` `projective` `theorem projectiveDynamics_tomitaAtomSeed_J_comp_eps` signals=[]
- `lean/InfoGeometry/Canonical/MajoranaKreinCartanSplit.lean:73` `projective` `theorem projectiveDynamics_tomitaAtomSeed_commute` signals=[]
- `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean:406` `projective` `theorem gaugeSectionFinProb_countRay_apply_toReal` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean:586` `projective` `theorem projectiveCountHamiltonianProfile_eq_relativeModularPotential_countRay` signals=[]
- `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean:910` `projective` `theorem projectiveLogGenerator_countRay_eq_projectiveCountHamiltonianProfile` signals=[]
- `lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean:753` `projective` `theorem relativeModularHamiltonian_sub_countMassShift_cocycle` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean:38` `projective` `theorem RestrictedRelativeModularData.local_projectiveLogGenerator_eq_local_modularPotential_ae` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean:68` `projective` `theorem RestrictedRelativeModularData.local_projectiveLogGenerator_eq_local_modularPotential` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean:93` `projective` `theorem RestrictedRelativeModularData.local_projectiveLogGenerator_eq_pullback_ambient_add_shift_ae` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean:117` `projective` `theorem RestrictedRelativeModularData.local_projectiveLogGenerator_eq_pullback_ambient_add_shift` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean:144` `projective` `theorem RestrictedRelativeModularData.local_modularPotential_eq_projectiveCountHamiltonianProfile_of_countRays` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean:167` `projective` `theorem RestrictedRelativeModularData.projectiveCountHamiltonianProfile_eq_pullback_ambient_add_shift` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean:202` `projective` `theorem RestrictedRelativeModularData.local_projectiveLogGenerator_eq_projectiveCountHamiltonianProfile_of_countRays` signals=[]
- `lean/InfoGeometry/Canonical/ModularKLDivergenceBridge.lean:43` `projective` `theorem generalizedKL_scale_shape_split` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/ModularKLDivergenceBridge.lean:59` `projective` `theorem generalizedKL_eq_klLike_add_massSlack` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/ModularKLDivergenceBridge.lean:72` `projective` `theorem generalizedKL_scale_shape_terms_nonneg` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/ModularKLDivergenceBridge.lean:99` `projective` `theorem generalizedKL_scale_shape_mass_term_pos_of_mass_ne` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/ModularKLDivergenceBridge.lean:116` `projective` `theorem generalizedKL_scale_shape_split_with_nonneg` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/ModularKLDivergenceBridge.lean:370` `projective` `theorem positiveRay_logGenerator_eq_relativeModularPotential_ae` signals=[]
- `lean/InfoGeometry/Canonical/ModularKLDivergenceBridge.lean:387` `projective` `theorem positiveRay_logGenerator_eq_relativeModularPotential` signals=[]
- `lean/InfoGeometry/Canonical/ModularKLDivergenceBridge.lean:402` `projective` `theorem positiveRay_logGenerator_eq_neg_relativeLogDensity` signals=[]
- `lean/InfoGeometry/Canonical/RelativeModularRecomposition.lean:59` `projective` `def PolarizedRecompositionData.plusLogDefect` signals=[]
- `lean/InfoGeometry/Canonical/RelativeModularRecomposition.lean:59` `projective` `def PolarizedRecompositionData.plusLogDefect` signals=[]
- `lean/InfoGeometry/Canonical/RelativeModularRecomposition.lean:59` `projective` `def PolarizedRecompositionData.plusLogDefect` signals=[]
- `lean/InfoGeometry/Canonical/RelativeModularRecomposition.lean:65` `projective` `def PolarizedRecompositionData.minusLogDefect` signals=[]
- `lean/InfoGeometry/Canonical/RelativeModularRecomposition.lean:71` `projective` `def PolarizedRecompositionData.couplingLogDefect` signals=[]
- `lean/InfoGeometry/Canonical/RelativeModularRecomposition.lean:77` `projective` `def PolarizedRecompositionData.couplingPotentialDefect` signals=[]
- `lean/InfoGeometry/Canonical/RelativeModularRecomposition.lean:88` `projective` `def PolarizedRecompositionData.sectorwiseExact` signals=[]
- `lean/InfoGeometry/Canonical/RelativeModularRecomposition.lean:88` `projective` `def PolarizedRecompositionData.sectorwiseExact` signals=[]
- `lean/InfoGeometry/Canonical/RelativeModularRecomposition.lean:95` `projective` `def PolarizedRecompositionData.vanishingCoupling` signals=[]
- `lean/InfoGeometry/Canonical/RelativeModularRecomposition.lean:128` `projective` `def PolarizedRecompositionData.recomposedAmbientModularPotential` signals=[]
- `lean/InfoGeometry/Canonical/RelativeModularRecomposition.lean:135` `projective` `def PolarizedRecompositionData.recomposedCommonCarrierLogDensity` signals=[]
- `lean/InfoGeometry/Canonical/RelativeModularRecomposition.lean:142` `projective` `def PolarizedRecompositionData.recomposedCommonCarrierModularPotential` signals=[]
- `lean/InfoGeometry/Canonical/RelativeModularRecomposition.lean:149` `projective` `def PolarizedRecompositionData.exactLogRecomposition` signals=[]
- `lean/InfoGeometry/Canonical/RelativeModularRecomposition.lean:156` `projective` `def PolarizedRecompositionData.exactPotentialRecomposition` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/OddDefectFunctional.lean:49` `projective` `theorem projectiveCountDefectFunctional_eq_countMassShift` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/OddDefectFunctional.lean:61` `projective` `theorem projectiveCountDefectFunctional_eq_neg_log_relativeVolumeChange` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/OddDefectFunctional.lean:83` `projective` `theorem projectiveCountDefectBarrier_nonneg` signals=['Nonempty']
- `lean/InfoGeometry/Canonical/ModularSurprisalThermoPacket.lean:49` `projective` `theorem representativeModularPotential_eq_negative_relativeLogDensity` signals=['Nonempty', 'Interface']
- `lean/InfoGeometry/Canonical/ModularSurprisalThermoPacket.lean:60` `projective` `theorem relativeModularPotential_eq_negative_relativeLogDensity` signals=['Nonempty', 'Interface']
- `lean/InfoGeometry/Canonical/DensityWeightIntertwinerBridge.lean:48` `projective` `def IsCriticalDensityWeight` signals=[]
- `lean/InfoGeometry/Canonical/DensityWeightIntertwinerBridge.lean:86` `projective` `theorem projectiveDensityWeightHamiltonianProfile_zero` signals=[]
- `lean/InfoGeometry/Canonical/DensityWeightIntertwinerBridge.lean:98` `projective` `theorem projectiveDensityWeightHamiltonianProfile_eq_relativeModularPotential_countRay_add_weightShift` signals=[]
- `lean/InfoGeometry/Canonical/RNDeterminantConnesChainBridge.lean:37` `projective` `theorem relativeDensity_state_chain` signals=['Interface']
- `lean/InfoGeometry/Canonical/RNDeterminantConnesChainBridge.lean:85` `projective` `theorem rn_state_chain` signals=['Interface']
- `lean/InfoGeometry/Canonical/FirstQuantizationProbability.lean:69` `projective` `theorem classicalSurprisal_eq_relativeModularPotential` signals=['Nonempty']
