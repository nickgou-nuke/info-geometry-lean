# Split `Cl(1,1)` Content Collision Map

This note is a **content-first** collision map for the local split `Cl(1,1)`
packet. It exists because filename inventory alone is not enough in this repo:
the same operator may appear under several names, and different operators may
share the same rhetoric.

Use this note together with:

- [BILINGUAL_SPINE_POLICY.md](BILINGUAL_SPINE_POLICY.md)
- [cl11_replica_inventory.md](cl11_replica_inventory.md)
- [cl11_rosetta_refactor_plan.md](cl11_rosetta_refactor_plan.md)

## Search Method

This map was built from **full-content search**, not filename guesses.

The full-codebase search covered exact names, legacy names, and semantic
synonyms for:

- `modular_j`, `modularConjugationJ`, `paritySuperchargeOp`, `chiralityOperator`
- `spectral_epsilon`, `modularSignEpsilon`, `modularSuperchargeOp`
- `complex_i`, `modularComplexI`, `dilationOperator`, `modularK`,
  `cptSuperchargeOp`
- `nullMinus`, `nullPlus`, `uMinus`, `uPlus`, `creation`, `annihilation`
- `gradePlusProj`, `gradeMinusProj`, `spectralPlusProj`, `spectralMinusProj`,
  `chiralityProjPlus`, `chiralityProjMinus`
- `cl11Rep`, `cl11RepHilbert`, `cl11RepNeutral`, `cl11RepLinear`

The classification rule is:

- **literal alias candidate**: same carrier and same defining term
- **genuine translation**: same algebra, but moved by realization, transport,
  tensor lift, projective descent, or carrier change

## Root Owner Packet

The root owner surface for the same-carrier doubled packet is:

- `lean/InfoGeometry/Krein/DoubledSpace.lean`
- `lean/InfoGeometry/Krein/Representation.lean`
- `lean/InfoGeometry/Clifford/Grading.lean`
- `lean/InfoGeometry/Clifford/Relations.lean`

At the content level, these files define the primitive doubled packet:

- `J := modular_j`
- `ε := spectral_epsilon`
- `K := complex_i = J.comp ε`
- `cl11Rep`
- grade projectors from `J`
- spectral projectors from `ε`

This is the safe root for same-carrier deduplication.

## Literal Alias Families

These are the high-confidence same-carrier collision families.

### `J` family

All of the following are same-carrier names for the same doubled operator, or
for a direct packaging of it:

- `modular_j`
- `modularConjugationJ := modular_j`
- `paritySuperchargeOp := modular_j`
- `chiralityOperator := modular_j`
- `(doubledSpaceCl11Action).J = modular_j`
- `cl11Rep (ι (1, 0)) = modular_j`

Dedup status:

- canonical owner name should remain `modular_j`
- Tomita and supercharge names are bilingual aliases, not new operators

### `ε` family

The following are same-carrier names for the same doubled operator, or direct
packagings of it:

- `spectral_epsilon`
- `modularSignEpsilon := spectral_epsilon`
- `modularSuperchargeOp := spectral_epsilon`
- `(doubledSpaceCl11Action).eps = spectral_epsilon`
- `cl11Rep` of the split pseudoscalar equals `spectral_epsilon`

Dedup status:

- canonical owner name should remain `spectral_epsilon`
- Tomita and supercharge names are aliases

### `K/Q` family

This is the largest same-carrier collision family.

Content evidence shows:

- `complex_i := modular_j.comp spectral_epsilon`
- `dilationOperator = complex_i`
- `modularComplexI := complex_i`
- `modularK = modularComplexI`
- `(doubledSpaceCl11Action).K = complex_i`
- `cl11Rep (ι (0, 1)) = complex_i`
- `(modularCPTSupercharge).Q = dilationOperator`
- `cptSuperchargeOp := (modularCPTSupercharge).Q`

So on the same doubled carrier, these are not independent operators. They are
different registers for the same square-minus-one axis.

Dedup status:

- canonical owner name should remain `complex_i` at the root
- `dilationOperator`, `modularComplexI`, `modularK`, and `cptSuperchargeOp`
  should be treated as translator/coherence vocabulary, not as new primitives

## Projector Families: Do Not Flatten Blindly

There are two genuinely different projector families on the same carrier.

### Grade projectors from `J`

These are the `±1` projectors for the geometric grading involution `J`:

- `gradePlusProj`
- `gradeMinusProj`
- `chiralityProjPlus := gradePlusProj`
- `chiralityProjMinus := gradeMinusProj`
- `creationLike := gradePlusProj`
- `annihilationLike := gradeMinusProj`

These should be deduplicated internally as one family.

Bridge status:

- the root alias bridge now exists explicitly in
  `lean/InfoGeometry/Krein/Prelude.lean`
- `chiralityProjPlus_eq_gradePlusProj`
- `chiralityProjMinus_eq_gradeMinusProj`
- so this family is no longer only an unfolding coincidence; it has named
  comparison theorems at the source

### Spectral projectors from `ε`

These are the `±1` projectors for `ε`:

- `spectralPlusProj`
- `spectralMinusProj`
- `StandardFormSeed.plusProjector (tomitaAtomSeed) = spectralPlusProj`
- `StandardFormSeed.minusProjector (tomitaAtomSeed) = spectralMinusProj`

These are **not** the same family as the `J`-grade projectors.

Refactor warning:

- do not merge grade projectors with spectral projectors
- they are different projector packets even when the prose uses the same words
  like "chirality", "sheet", or "sector"

## Null-Mode Families

These are related, but they live in different registers and must not be fused
naively.

### Abstract split-`Cl(1,1)` atom

- `nullMinus`
- `nullPlus`

in `lean/InfoGeometry/Clifford/SplitQ11PhaseFlip.lean`

### Concrete mode vectors on the doubled Majorana core

- `cl11_uMinus`
- `cl11_uPlus`

in `lean/InfoGeometry/Quantum/RealMajoranaCategory.lean`

### Tensor/Bott head lift

- `headNullMinusTensor`
- `headNullPlusTensor`

in `lean/InfoGeometry/Canonical/SplitCliffordHeadLift.lean`

### Continuous CAR operators

- `concreteCARAnnihilation`
- `concreteCARCreation`

in `lean/InfoGeometry/Canonical/SuperchargeCARCCRBridge.lean`

These are a genuine translation chain:

`abstract null modes -> concrete mode vectors -> tensor/head lift -> continuous CAR operators`

Refactor warning:

- these are not alias duplicates
- they are the same algebra in different realization layers

## Projector-Super Pair vs Genuine CAR Pair

The repo already distinguishes a dangerous false duplicate.

In `lean/InfoGeometry/Canonical/BogoliubovFockSuper.lean`:

- `annihilationOp` and `creationOp` are a projector-super pair
- they are **not** the same as the genuine concrete CAR pair

So these must stay separate:

- `annihilationOp` / `creationOp`
- `concreteCARAnnihilation` / `concreteCARCreation`

Refactor warning:

- same vocabulary does not mean same algebra
- the former is a doubled-projector model
- the latter is the true `Cl(1,1)` CAR realization

## Finite / Hilbert / Neutral Wrappers

These are not root duplicates to delete.

### `HilbertDoubled`

`HilbertDoubled` is a type-distinct wrapper:

- `HilbertDoubled := ULift (DoubledSpace E)`

So `cl11RepHilbert` and `cl11RepLinHilbert` are **transported wrapper
implementations**, not same-carrier aliases.

Bridge status:

- the carrier bridge is explicit in `lean/InfoGeometry/Krein/HilbertBridge.lean`
- `HilbertDoubled.ofDoubledLIE`
- `HilbertDoubled.toDoubledLIE`
- `HilbertDoubled.ofDoubledContinuousLinearEquiv`
- `HilbertDoubled.toDoubledContinuousLinearEquiv`
- with new pointwise bridge lemmas:
  - `HilbertDoubled.ofDoubledLIE_apply`
  - `HilbertDoubled.toDoubledLIE_apply`
  - `HilbertDoubled.ofDoubledContinuousLinearEquiv_apply`
  - `HilbertDoubled.toDoubledContinuousLinearEquiv_apply`
- the wrapper alias in `lean/InfoGeometry/Krein/DoubledAdjoint.lean` is now
  explicit too:
  - `doubledToHilbert_eq_ofDoubledContinuousLinearEquiv`
  - `doubledToHilbert_apply`
- the generator transport is explicit in `lean/InfoGeometry/Krein/Clifford.lean`
  - `toDoubled_hilbertSwapCLM_apply`
  - `toDoubled_jCLM_apply`
  - `toDoubled_hilbertComplexI_apply`

Interpretation:

- the Hilbert carrier realizes the same local split algebra on a wrapper
  carrier
- but its primitive generator presentation is not a same-name copy of the
  doubled owner packet
- the transport shows:
  - Hilbert grading `hilbertSwapCLM` carries `modular_j`
  - Hilbert Krein symmetry `jCLM` carries `spectral_epsilon`
  - Hilbert complex generator `hilbertComplexI` carries `complex_i`
- so this is a genuine transported presentation, not a literal duplicate of
  `cl11Rep` on `DoubledSpace`

### `NeutralSpace`

`NeutralSpace` is also a type-distinct wrapper:

- `NeutralSpace := ULift (DoubledSpace E)`

with a nontrivial `rotation45` bridge.

So `cl11RepNeutral` is not a same-carrier duplicate. It is a transported
representation along the 45-degree bridge.

Bridge status:

- the carrier bridge is explicit in `lean/InfoGeometry/Krein/HilbertBridge.lean`
- the neutral wrapper alias is explicit too:
  - `neutralJ_eq_J`
- `NeutralSpace.rotation45`
- `NeutralSpace.rotation45Isometry`
- `NeutralSpace.rotation45ToHilbert`
- `NeutralSpace.rotation45ToHilbertContinuousLinearEquiv`
- the representation transport is explicit in
  `lean/InfoGeometry/Krein/Clifford.lean`
  - `rotation45_cl11RepNeutral_apply`
  - `rotation45_gradeCLM_neutral_apply`
- with new pointwise carrier lemmas:
  - `NeutralSpace.rotation45ToHilbert_apply`
  - `NeutralSpace.rotation45ToHilbertContinuousLinearEquiv_apply`

Refactor rule:

- keep these as explicit transported implementations
- if renamed later, use a transport-marking suffix, not a canonical owner name

## Linear vs Continuous Representation

`cl11RepLinear` in `RealMajoranaCategory` is also not a new representation.
It is the continuous owner forgotten to linear maps:

- `cl11RepLinear a := (cl11Rep a).toLinearMap`

Refactor rule:

- classify as translator/forgetful view, not duplicate owner

## Genuine Translation Families

These are the content-level packets that should remain as parallel lawful
presentations.

### Abstract split atom

- `SplitQ11PhaseFlip`
- `SplitQ11Projectors`

## Owner-Normalized Phase-Axis Surface

The live transport/readout lane now has an explicit owner-name theorem surface
using `InfoGeometry.Krein.complex_i`, while preserving the older
`modularComplexI` API.

Stable owner companions now exist in:

- `lean/InfoGeometry/Canonical/TomitaTakesaki.lean`
  - `complex_i_inner_skew`
  - `complex_i_inner_comp`
- `lean/InfoGeometry/Canonical/StateDependentTransport.lean`
  - `stateQGTPhaseReadout_eq_metric_comp_complex_i`
- `lean/InfoGeometry/Canonical/RelationalInformationCore.lean`
  - `channelPhaseAxis_apply_eq_comp_complex_i`
  - `comparisonPhaseReadout_eq_metric_comp_complex_i`
- `lean/InfoGeometry/Canonical/RelativeModularPotential.lean`
  - `comparisonPhaseReadout_eq_metric_comp_complex_i`
  - `comparisonStateGeneratorPhase_apply_eq_comp_complex_i`
  - `toRelationalInformationDatum_comparisonGeneratorPhase_apply_eq_comp_complex_i`
- `lean/InfoGeometry/Canonical/RelationalInformationDynamics.lean`
  - `constructiveRelationalDatum_comparisonGeneratorPhase_apply_eq_comp_complex_i`
  - `operatorInformationPhaseReadout_eq_metric_comp_complex_i`
- `lean/InfoGeometry/Canonical/OperatorialUncertainty.lean`
  - `inner_sq_add_complex_i_inner_sq_le`
  - phase-linear comparison-state proofs now use the owner `complex_i` packet in
    their core evaluation steps
- `lean/InfoGeometry/Quantum/GeometricTensorTransport.lean`
  - `KRotation_preserves_inner_complex_i`
- `lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean`
  - `berryTwoFormJEpsOfOperator_apply_root`
  - `berryOfOperator_apply_complex_i`
  - `metricOfOperator_complex_i_skew_of_commutesWith_complex_i`
  - `metricOfOperator_spectral_epsilon_comp_eq_kreinMetricOfOperator`
  - `inner_spectral_epsilon_apply_eq_kreinInner`
  - `inner_apply_spectral_epsilon_eq_kreinInner`
  - `modularVarianceSeed_eq_spectral_epsilon_comp`
  - `isSelfAdjoint_spectral_epsilon_comp_of_kreinSelfAdjoint`
  - `isPhaseLinear_spectral_epsilon_comp_of_IsPhaseAntilinear`
  - `qgtOfOperator_spectral_epsilon_comp_metric_eq_kreinQgtOfOperator_metric`
  - `qgtOfOperator_spectral_epsilon_comp_berry_eq_kreinQgtOfOperator_berry`
  - `complex_i_star_eq_neg`
- `lean/InfoGeometry/Canonical/SplitCliffordTensorBridge.lean`
  - `doubledHeadAtom_supergradedLiePackage_root`
- `lean/InfoGeometry/Canonical/ConnesArakiTomita.lean`
  - `topologicalBekensteinBound_and_tomitaModularKMS_of_tomitaConnesArakiData_root`
- `lean/InfoGeometry/Canonical/OnsagerCasimirJ.lean`
  - `complex_i_comp_modularConjugationJ`
- `lean/InfoGeometry/Canonical/CoordinateFreeSecondVariation.lean`
  - `modularCurvatureOperator_eq_metricPart_complex_i`
- `lean/InfoGeometry/Canonical/BohmMadelungOperatorialBridge.lean`
  - `stateGeneratorField_phaseReadout_eq_metric_comp_complex_i`
  - retained bilingual export:
    `stateGeneratorField_phaseReadout_eq_metric_comp_K`
- `lean/InfoGeometry/Canonical/FisherVolumeBridge.lean`
  - `metric_to_phase_readout_bridge_comp_complex_i`
  - deprecated bilingual alias:
    `metric_to_phase_readout_bridge`

Supporting wrapper reroute now landed in:

- `lean/InfoGeometry/Canonical/RelativeModularPotential.lean`
  - local proof bodies for comparison-generator phase wrappers now route through
    the existing core phase-axis surface instead of re-proving the phase packet
    ad hoc
  - deprecated bilingual aliases:
    `comparisonStateGeneratorPhase_apply`
    `toRelationalInformationDatum_comparisonGeneratorPhase_apply`
- `lean/InfoGeometry/Canonical/OnsagerReciprocity.lean`
  - the alternating phase-sector proof is being rerouted to the root
    `complex_i` packet through explicit bridge names

Refactor rule:

- downstream files with public theorem statements mentioning `modularComplexI`
  may stay unchanged for API stability
- new proofs and bridge files should prefer the `complex_i` owner surface where
  possible
- wrapper theorem statements can be migrated only after a bridge-first consumer
  pass
- `SplitQ11Equivariance`

### Doubled realization

- `DoubledSpace`
- `Representation`
- `RealSplitClifford`

### Bott/tensor recursion

- `BottPeriodicity`
- `SplitCliffordTensorBridge`
- `SplitCliffordHeadLift`
- `SplitCliffordHeadPolarization`
- `SplitCliffordHeadPhaseFlip`

### Projective descent

- `ProjectiveRays`
- `Krein/State`
- `Projective/Dynamics`
- `ProjectiveSplitQ11Realization`

### Operatorial supercharge/Fock lane

- `BogoliubovFockSuper`
- `SuperchargeCARCCRBridge`
- `SuperchargeRoleBridge`
- `ProjectorEquivariance`
- `SuperchargeGapHessianBridge`
- `OperatorialCentralCharge`

### BdG/DIII lane

- `RealBdG`
- `RealBdGSheetBridge`
- `RealBdGDIIIAtom`

These are not to be flattened into one file or one name family.

## Root-First Dedup Queue

Safe root-first deduplication should proceed in this order.

1. Same-carrier alias cleanup
   - `modular_j` family
   - `spectral_epsilon` family
   - `complex_i` family

2. Same-carrier projector alias cleanup
   - `gradePlusProj` / `gradeMinusProj`
   - `chiralityProjPlus` / `chiralityProjMinus`

3. Preserve translated implementations
   - `cl11RepHilbert`
   - `cl11RepNeutral`
   - `cl11RepLinear`
   - Bott/head packet
   - projective packet

4. Preserve genuine algebra distinctions
   - grade projectors vs spectral projectors
   - projector-super pair vs genuine CAR pair

5. Only after bridge/reroute completion
   - rename legacy aliases
   - deprecate wrappers
   - remove consumers of old names

Short rule:

**dedup same-carrier aliases first; preserve transported realizations and real
algebra distinctions.**

## Recently Landed Owner-Name Companions

- `TomitaTakesaki`
  - `complex_i_inner_skew`
  - `complex_i_inner_comp`
- `RelativeModularPotential`
  - `comparisonPhaseReadout_eq_metric_comp_complex_i`
  - `comparisonStateGeneratorPhase_apply_eq_comp_complex_i`
  - `toRelationalInformationDatum_comparisonGeneratorPhase_apply_eq_comp_complex_i`
- `RelationalInformationDynamics`
  - `constructiveRelationalDatum_comparisonGeneratorPhase_apply_eq_comp_complex_i`
  - `operatorInformationPhaseReadout_eq_metric_comp_complex_i`
- `OperatorialUncertainty`
  - `inner_sq_add_complex_i_inner_sq_le`
  - phase-linear core proofs rerouted to `complex_i`
- `GeometricTensorTransport`
  - `KRotation_preserves_inner_complex_i`
  - proof-body transport reroutes now use
    `complex_i_comp_modularTransportFlow_eq_modularTransportFlow_comp_complex_i_of_IsPhaseLinear`
    and
    `modularTransportFlow_eq_KRotation_of_generator_eq_smul_complex_i`
- `GeometricTensorOperatorLift`
  - `berryTwoFormJEpsOfOperator_apply_root`
  - `berryOfOperator_apply_complex_i`
  - `metricOfOperator_spectral_epsilon_comp_eq_kreinMetricOfOperator`
  - `inner_spectral_epsilon_apply_eq_kreinInner`
  - `inner_apply_spectral_epsilon_eq_kreinInner`
  - `modularVarianceSeed_eq_spectral_epsilon_comp`
  - `isSelfAdjoint_spectral_epsilon_comp_of_kreinSelfAdjoint`
  - `isPhaseLinear_spectral_epsilon_comp_of_IsPhaseAntilinear`
  - `qgtOfOperator_spectral_epsilon_comp_metric_eq_kreinQgtOfOperator_metric`
  - `qgtOfOperator_spectral_epsilon_comp_berry_eq_kreinQgtOfOperator_berry`
  - `metricOfOperator_complex_i_skew_of_commutesWith_complex_i`
  - `complex_i_star_eq_neg`
- `SplitCliffordTensorBridge`
  - `doubledHeadAtom_supergradedLiePackage_root`
- `ConnesArakiTomita`
  - `topologicalBekensteinBound_and_tomitaModularKMS_of_tomitaConnesArakiData_root`
- `OnsagerCasimirJ`
  - `complex_i_comp_modularConjugationJ`
- `CoordinateFreeSecondVariation`
  - `modularCurvatureOperator_eq_metricPart_complex_i`
- `BohmMadelungOperatorialBridge`
  - `stateGeneratorField_phaseReadout_eq_metric_comp_complex_i`
  - retained bilingual export:
    `stateGeneratorField_phaseReadout_eq_metric_comp_K`
- `FisherVolumeBridge`
  - `metric_to_phase_readout_bridge_comp_complex_i`
- `BogoliubovProjectorTransport`
  - owner-name companions for projector transport and sheet maps:
    `spectral_epsilon_comp_spectralPlusProj`,
    `spectral_epsilon_comp_spectralMinusProj`,
    `spectralPlusProj_comp_spectral_epsilon`,
    `spectralMinusProj_comp_spectral_epsilon`,
    `spectralPlusProj_comp_modular_j`,
    `spectralMinusProj_comp_modular_j`,
    `spectralPlusProj_comp_complex_i`,
    `spectralMinusProj_comp_complex_i`,
    `modular_j_maps_plusSheet_to_minusSheet`,
    `modular_j_maps_minusSheet_to_plusSheet`,
    `complex_i_maps_plusSheet_to_minusSheet`,
    `complex_i_maps_minusSheet_to_plusSheet`
- `BogoliubovClosedForms`
  - owner-name companions for exact closed forms and action formulas:
    `JBoost_eq_cosh_add_sinh_modular_j`,
    `epsilonBoost_eq_cosh_add_sinh_spectral_epsilon`,
    `KRotation_eq_cos_add_sin_complex_i`,
    `JBoost_apply_modular_j`,
    `epsilonBoost_apply_spectral_epsilon`,
    `KRotation_apply_complex_i`,
    `spectral_epsilon_comp_epsilonBoost`,
    `spectral_epsilon_comp_JBoost`,
    `spectral_epsilon_comp_KRotation`
- `BogoliubovTransport`
  - owner-name companions for transport-core phase-axis logic:
    `isPhaseLinear_iff_comp_complex_i`,
    `isPhaseAntilinear_iff_comp_complex_i`,
    `phaseAxisForce_eq_transportCommutator_complex_i`,
    `complex_i_commutes_modularTransportGenerator_of_IsPhaseLinear`,
    `complex_i_comp_modularTransportFlow_eq_modularTransportFlow_comp_complex_i_of_IsPhaseLinear`,
    `modularTransportFlow_eq_KRotation_of_generator_eq_smul_complex_i`
- `BogoliubovProjectorFlux`
  - owner-name companions for transported projectors and flux packets:
    `JBoost_comp_spectralPlusProj_modular_j`,
    `JBoost_comp_spectralMinusProj_modular_j`,
    `KRotation_comp_spectralPlusProj_complex_i`,
    `KRotation_comp_spectralMinusProj_complex_i`,
    `transportedPlusProjector_JBoost_modular_j`,
    `transportedMinusProjector_JBoost_modular_j`,
    `transportedPlusProjector_KRotation_complex_i`,
    `transportedMinusProjector_KRotation_complex_i`,
    `plusProjectorFlux_JBoost_modular_j`,
    `minusProjectorFlux_JBoost_modular_j`,
    `plusProjectorFlux_KRotation_complex_i`,
    `minusProjectorFlux_KRotation_complex_i`
- `RestrictedVolumeCharacter`
  - `dualSheetDiagonalScalarOp_one_neg_one_eq_spectral_epsilon`
  - `chiralDilationPartCore`
  - `chiralDilationPart_eq_core`
  - `dualSheetDiagonalScalarOp_exp_pair_eq_epsilonBoost_core`
- `PolarizedMadelungBridge`
  - `phaseOrbit_eq_complex_iOrbit`
  - `modular_j_phaseOrbit_eq_reverse_complex_i`
  - `statePhaseReadout_eq_metric_comp_complex_i`
- `VortexAnomalyLink`
  - legacy `VortexPair` fields remain typed against the older
    `modularConjugationJ` / `modularSignEpsilon` surface
  - owner-name bridge companions now expose the same packet through the root names:
    `canonicalVortexPair_source_comm_spectral_epsilon`,
    `canonicalVortexPair_sink_comm_spectral_epsilon`,
    `canonicalVortexPair_source_comp_modular_j`,
    `canonicalVortexPair_sink_comp_modular_j`
- `HestenesKahler`
  - retains the Majorana/Hestenes translation surface
  - owner-name companion theorems now expose the same phase packet through the root names:
    `K_eq_complex_i`,
    `certifiedProjectorObstructionStatePhaseReadout_eq_metric_comp_complex_i`,
    `starCertifiedEinsteinAnomalyStatePhaseReadout_eq_metric_comp_complex_i`
  - deprecated bilingual aliases:
    `certifiedProjectorObstructionStatePhaseReadout_eq_metric_comp_K`,
    `starCertifiedEinsteinAnomalyStatePhaseReadout_eq_metric_comp_K`
- `CliffordDictionary`
  - remains the legacy-semantics dictionary surface
  - canonical root-name companions now identify the same local packet via:
    `canonical_eps_eq_spectral_epsilon`,
    `canonical_J_eq_modular_j`,
    `canonical_K_eq_complex_i`,
    `chiralityObservable_eq_operatorObservable_spectral_epsilon`,
    `phaseObservable_eq_operatorObservable_complex_i`
- `StandardFormCore`
  - canonical standard-form seed remains the legacy packaging surface
  - root-name companions now expose the same atom through:
    `tomitaAtomSeed_J_eq_modular_j`,
    `tomitaAtomSeed_eps_eq_spectral_epsilon`,
    `tomitaAtomSeed_phaseAxis_eq_complex_i`
- `GeneralizedMetricCore`
  - canonical generalized-metric seed remains the legacy packaging surface
  - root-name companions now expose the same atom through:
    `tomitaGeneralizedMetricSeed_eta_eq_modular_j`,
    `tomitaGeneralizedMetricSeed_polarization_eq_spectral_epsilon`,
    `tomitaGeneralizedMetricSeed_metricOperator_eq_complex_i`
- `GeometricTensor`
  - the QGT owner surface remains stated in the legacy phase-axis language
  - root-name compatibility companions now expose the same packet through:
    `compat_complex_i`,
    `ofMajorana_compat_complex_i`
- `GeometricTensorTest`
  - regression tests now include the owner-name compatibility witness:
    `ofMajorana_compat_complex_i`
- `RosettaSourceBridge`
  - root-name real-Majorana phase-axis bridge:
    `complex_i_toLinearMap_eq_realMajoranaKAxis`
- `QuantumLieAlgebroidRosetta`
  - root-name companions now expose the internal phase axis packet through:
    `internalPhaseAxis_eq_complex_i`,
    `paper_phaseReadout_eq_metric_comp_complex_i`
- `DensityWeightIntertwinerBridge`
  - root-name companion:
    `densityWeightPhaseAxis_eq_complex_i`
  - deprecated bilingual alias:
    `densityWeightPhaseAxis_eq_modularComplexI`
- `BerryConnection`
  - Hestenes/Kaehler bridge now exposes the root owner packet through:
    `SuperHestenesKaehlerDatum.K_eq_complex_i`,
    `SuperHestenesKaehlerDatum.toQGT_compat_complex_i`,
    `SuperHestenesKaehlerDatum.ofQGT_J_eq_modular_j`,
    `SuperHestenesKaehlerDatum.ofQGT_epsilon_eq_spectral_epsilon`,
    `SuperHestenesKaehlerDatum.ofQGT_K_eq_complex_i`,
    `hestenesBerryTwoForm_apply_complex_i`,
    `deriv_berryOfOperator_phaseAxisTransport_at_zero_eq_berryOf_phaseAxisResponse_complex_i`,
    `deriv_berryOfOperator_phaseAxisTransport_at_zero_eq_berryOf_two_smul_comp_complex_i_of_IsPhaseAntilinear`
- `RealBdG`
  - root-name companion for the real BdG phase packet:
    `modularK_eq_modular_j_comp_spectral_epsilon`
- `Quantum/HestenesKahler`
  - projective/Hestenes packet now exposes the same root owner surface through:
    `J_eq_modular_j`,
    `eps_eq_spectral_epsilon`,
    `compat_complex_i`,
    `comp_complex_i_isPhaseAntilinear`
- `RealBdGDIIIAtom`
  - canonical DIII proxy now exposes the root owner packet through:
    `cptSuperchargeOp_eq_modularK_root`,
    `canonicalDIIIProxy_S_eq_neg_spectral_epsilon`,
    `canonicalDIIIProxy_T_eq_modularK`,
    `canonicalDIIIProxy_T_eq_complex_i`,
    `canonicalDIIIProxy_C_eq_modular_j`
  - root-name packaged DIII laws and closure:
    `canonicalDIIIProxy_root_laws`,
    `canonicalDIIIProxy_transport_root_closure`
- `Physics/DIIISymmetryAtom`
  - raw DIII translator now exposes the same root packet through:
    `cl11DIIIPackage_T_eq_complex_i`,
    `cl11DIIIPackage_C_eq_modular_j`,
    `cl11DIIIPackage_root_laws`
- `OperatorAlgebraModularAtom`
  - root-name split-`Cl(1,1)` witness:
    `modular_atom_is_cl11_root`
- `WeylGaugeOperatorLift`
  - root-name logarithmic-generator companion:
    `logarithmicGenerator_eq_common_plus_relative_spectral_epsilon`
- `ModularAnomaly`
  - root-name companions now expose the modular-shadow packet through:
    `canonicalCl11Generator_eq_spectral_epsilon`,
    `expFlow_modular_j_eq_sigmaMap`,
    `latticeAvatar_modular_j`,
    `latticeAvatar_sigmaMap_modular_j`,
    `latticeAvatar_exp_modular_j`
- `SuperchargeCARCCRBridge`
  - root-name companions now expose the same supercharge carrier packet through:
    `cptSuperchargeOp_eq_modular_j_comp_spectral_epsilon`,
    `modular_j_spectral_epsilon_car_zero`,
    `modular_j_spectral_epsilon_ccr_eq_two_complex_i`,
    `complex_i_sq`,
    `complex_i_maps_plus_to_minus`,
    `complex_i_maps_minus_to_plus`
- `SuperchargeRoleBridge`
  - root-name transport companions now expose the same role packet through:
    `transportedParitySupercharge_zero_eq_modular_j`,
    `transportedModularSupercharge_zero_eq_spectral_epsilon`,
    `transportedParityModularGapSeed_eq_car_root`,
    `transportedParityModularGapSeed_eq_phaseAntilinearCAR_root_of_commute_phaseLinearPart`,
    `deriv2_transportedParitySupercharge_at_zero_eq_operatorInformationHessian_of_modular_j`,
    `deriv2_transportedParitySupercharge_at_zero_eq_metricPart_add_half_curvaturePart_of_modular_j`
- `SuperchargeGapHessianBridge`
  - root-name closure package:
    `transported_gapSeed_hessian_curvature_root_package`
- `SuperchargeCentralChargeClosure`
  - root-name transport/central-charge closure surface:
    `rootGapHessianClosure`,
    `rootGapHessianClosure_iff_cptGapHessianClosure`,
    `root_gap_hessian_centralCharge_closure`
- `TopologicalInvariantInvariance`
  - scalar-shadow readout now exposes the root packet through:
    `quasilatticeAnalyticalIndex_eq_operatorialCentralCharge`
- `TopologicalResidue`
  - root analytical-index presentation of the residue lane:
    `wittenIndexResidue_eq_analyticalIndex_modular_j`,
    `canonicalSuperchargeMultiplet_wittenIndexResidue_eq_zero`
- `CentralChargeAnomaly`
  - upgraded to operatorial transport bridge over KK/Fredholm owners:
    `centralCharge_eq_transport_slice`,
    `isAnomalyFree_iff_transportSlice_eq_wittenIndexResidue`,
    `transportSlice_ne_zero_of_centralCharge_ne_zero`
- `Rosetta`, `DeepHorizon`, `RedLine`
  - residual legacy-name mentions are now paired with explicit root-name exports:
    `modular_j`, `spectral_epsilon`, `complex_i`
  - these are intentional bilingual reference surfaces, not owner-layer duplicates
