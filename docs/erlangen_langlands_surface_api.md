# Operator-Erlangen + Langlands Surface API

This is the theorem-surface index for the lane modules.

Legend:
- **S**: theorem-safe in-file proof.
- **W**: witness-gated/socket/assumption layer.
- **D**: definitional/construction scaffold (structures/defs).

Import this list by first loading
`lean/InfoGeometry/ErlangenLanglandsLane.lean`.

## `InfoGeometry.Geometry.BilingualUpperHalfPlane`
- **D** `DoubledEnd`, `PhaseLinear`, `moebius_action`, `moebiusMap`, `BilingualUpperHalfPlane`
- **S** `map_K`, `comp`, `add`, `phase_linear_apply`, `K_positivity_apply`,
  `denominator_phase_linear`, `moebius_action_phase_linear`,
  `moebiusMap_tau`, `moebiusMap_phase_linear`, `moebiusMap_K_positivity`
- **W** none explicit; this file is a geometric core for future operatorial embeddings.

## `InfoGeometry.OperatorAlgebra.FiniteJonesErlangerBridge`
- **D** `DiagonalJonesGauge`, `mat`, `invMat`, `conjugate`,
  `brewsterCoreProjector`, `brewsterNilProjector`,
  `FiniteJonesErlangerInvariant`, `brewsterCoreInvariant`,
  `generalJonesConjugate`, `transportedBrewsterCoreProjector`,
  `FiniteJonesErlangerBridgeOwnerTarget`
- **S** `diagJones_mul`, `diagonalGauge_conjugate_diagJones`,
  `DiagonalJonesGauge.mat_mul_invMat`, `DiagonalJonesGauge.invMat_mul_mat`,
  `diagonalGauge_preserves_brewsterCoreProjector`,
  `diagonalGauge_preserves_brewsterNilProjector`,
  `diagonalGauge_preserves_brewsterEvent_jones`,
  `diagonalGauge_brewster_det_zero`,
  `brewsterCoreProjector_is_fixed_Erlanger_object`
- **W** none; owner target is packaged as a definition/theorem pair but with explicit dependencies.

## `InfoGeometry.OperatorAlgebra.VerifiedCasimir`
- **D** `VerifiedCasimir`
- **S** `mem_center`, `mem_invariantSubring`
- **W** none

## `InfoGeometry.OperatorAlgebra.ConformalCyclicCosmology`
- **D** `AeonConformalCrossover`, `IsSelfDualCrossoverState`, `SurvivingConformalReadout`,
  `KitaevLikeBoundaryMemoryBridge`, `GenesisReentanglementBridge`,
  `CrossoverMemoryRecoveryBridge`, `LinearAeonReset`, `Survivor`, `AntiSurvivor`
- **S** `inverted_old_null`, `newCarrier_sameRay_inverted_old`, `selfDual_fixed_or_antiFixed`,
  `old_read_eq_inverted_old_read`, `old_symmetrized_readout_swaps`,
  `grammar_eq_on_crossover`, `edge_memory_matches_new_grammar`,
  `old_grammar_reentangles`, `genesis_split_valid`,
  `residue_recovers_old_memory`, `diagonal_survives`,
  `anti_diagonal_is_antiSurvivor`
- **W** explicit comment: recovery/crosswalk requires optional witness, not automatic cosmology physics claim.

## `InfoGeometry.OperatorAlgebra.KapustinWittenDualitySocket`
- **D** `WilsonLedger`, `THooftLedger`, `SDualityDatum`, `PairingDualityDatum`,
  `GeometricLanglandsInterpretation`, `ExceptionalSymmetrySocket`,
  `OperatorSDualityOwnerTarget`
- **S** `wilsonEigen_transports_to_tHooftEigen`, `tHooft_readout_eq_wilson_readout`,
  `electricPairing_eq_magneticPairing`, `geometric_langlands_valid`,
  `operatorSDualityOwnerTarget`
- **W** geometric Langlands layer is explicitly a socket; model must supply curve/group/sheaf data.

## `InfoGeometry.OperatorAlgebra.PhysicalLanglandsHolonomy`
- **D** `WilsonReadoutDatum`, `THooftReadoutDatum`, `LanglandsDualPair`,
  `KWPhysicalDualityWitness`, `RelationalKWPhysicalDualityWitness`,
  `KMSHolonomyCompatibility`, `DualHolonomyRecoveryWitness`,
  `PhysicalGeometricLanglandsInterpretation`,
  `PhysicalLanglandsHolonomyOwnerTarget`, `PhysicalLanglandsRecoveryOwnerTarget`,
  `DualHolonomyRecoveryInstalledTarget`
- **S** `wilson_readout_eq_dual_thooft`, `dual_thooft_eq_wilson_readout`,
  `wilson_rel_dual_thooft`, `electricKMS_eq_dualKMS`,
  `holonomy_and_kms_payload`, `recovered_*`, `dualHolonomy_ne_of_hiddenMemory_ne`,
  `wilsonReadout_ne_of_hiddenMemory_ne`,
  `hiddenMemory_recovered_from_wilson_of_KW`, `holonomy_kms_recovery_payload`,
  `geometric_langlands_valid`, owner target theorems
- **W** no construction of KMS or geometric Langlands; transport/recovery are supplied-witness theorems.

## `InfoGeometry.OperatorAlgebra.KleinianReturn`
- **D** `ProjectiveTomitaReturn`, `NonOrientableReturnInterpretation`
- **S** `observable_returns_to_commutant`
- **W** no claim that any `Cl(1,1)` is literally Klein bottle; orientation-return is supplied as interpretation.

## `InfoGeometry.OperatorAlgebra.SelfDualChiralConeBoundary`
- **D** `SelfDualChiralConeBoundary`, `FixedBoundary`, owner target def
- **S** `cone_eq_dualCone`, `boundary_preserved_reverse`,
  `left_boundary_maps_to_right_boundary`, `right_boundary_maps_to_left_boundary`,
  `mem_fixedBoundary_iff`, `boundaryOf_of_mem_fixedBoundary`,
  `theta_eq_self_of_mem_fixedBoundary`, `mem_fixedBoundary_of_boundary_fixed`,
  `closure_of_fixedBoundary`, `swapped_boundary_diagonal_fixed`,
  `swapped_boundary_imbalance_anti_fixed`,
  owner target theorem
- **W** boundary/return interpretation is witness-gated for physical/categorical identifications.

## `InfoGeometry.Automorphic.AutomorphicKreinBridge`
- **D** `AutomorphicKreinBridge`, `IsPCuspidal`
- **S** `cuspidalProjector_yields_PCuspidal`,
  `PCuspidal_iff_monogenic_readout`
- **W** conceptual bridge from automorphic surgery to Krein space is theorem-bearing but boundary semantics are intentionally constrained.

## `InfoGeometry.Automorphic.LFunctionResonance`
- **D** `AutomorphicOperatorIntertwining`, `IsCuspidalLanglandsLFunctional`,
  `CuspidalLFunctionDatum`, `IsBoundaryScatteringLFunctional`,
  `BoundaryScatteringLFunctionDatum`, `CompatibleAutomorphicOperatorFamily`,
  `HasCuspidalEigenpacket`, `HasHeckeEulerCompatibility`,
  `AutomorphicLResonanceWitness`, `AutomorphicLResonanceAdmissible`,
  `AutomorphicLResonanceOwnerTarget`
- **S** commutation/projection theorems on cuspidal/projectors/eigenspaces, including
  `boundaryProjector_commutes`, `cuspidalProjector_commutes`,
  `maps_ker_siegel_to_ker_siegel`, `cuspidalLFunction_*`, `boundaryScatteringLFunction_*`,
  `automorphicLResonanceWitness_nonempty_of_admissible`
- **W** header explicitly states no Euler product, functional equation, spectral theorem, or zero theorem; these are witness layers.

## `InfoGeometry.Automorphic.ProjectedLFunction`
- **D** `AutomorphicLFunctional`, `rawLFunction`, `boundaryLFunction`, `cuspidalLFunction`,
  `IsAutomorphicResonance`, `AutomorphicResonanceSet`,
  `ProjectedAutomorphicLFunctionWitness`, `EulerProductWitness`,
  `CompletedLFunctionWitness`, `LanglandsPrimeResonanceStrongWitness`,
  `LanglandsSugawaraBridge`, `ProjectedAutomorphicLFunctionOwnerTarget`,
  `LanglandsPrimeResonanceOwnerTarget`
- **S** projector/additivity and decomposition lemmas (`rawLFunction_eq_boundary_add_cuspidal`, etc.),
  witness bridge lemmas (`euler_product_valid`, `completed_functional_equation_valid`),
  calibration theorem `hiddenMemory_arithmetic_calibration`,
  owner target proofs
- **W** functional-equation/euler-product steps are explicitly certificate sockets.

## `InfoGeometry.Automorphic.RoelckeSelbergSpectral`
- **D** `CommuteLinear`, `shiftedOperator`, `eigenspace`, `cuspidalEigenspace`,
  `RoelckeSelbergSpectralDatum`, `JointEigenvalue`, `jointEigenspace`,
  `CuspidalEigenpacket`, `AutomorphicLFunctionDatum`,
  `potential`, `valueOnPacket`, `potentialOnPacket`,
  owner target defs
- **S** eigenspace membership lemmas (`mem_eigenspace_iff`, `mem_cuspidalEigenspace_iff`,
  `mem_jointEigenspace_iff`), preservation lemmas (`laplacian_mem_pCuspidal`, `hecke_mem_pCuspidal`,
  `laplacian_eigen`, `hecke_eigen`), `siegel_zero`, potential consistency lemmas.
- **W** packaged analytic spectral theorem as data/witness, not re-proved in-file.

## `InfoGeometry.Automorphic.LanglandsSugawaraBridge`
- **D** `LanglandsSugawaraBridge`, `toLanglandsPrimeResonanceWitness`,
  `LanglandsSugawaraBridgeInstalledTarget`
- **S** `centralCharge_eq_completedL`, `centralCharge_eq_hiddenGradeMemory`,
  `hiddenGradeMemory_eq_completedL`, install-theorem
- **W** witness-gated bridge; does not claim full Langlands/functoriality.

## `InfoGeometry.Automorphic.LanglandsPrimeResonance`
- **D** `CompletedLReadout`, `SugawaraCentralReadout`, `IsBoundaryLZero`, `HasCentralZero`,
  `IsBulkLanglandsPrimeResonance`, `HasBulkSugawaraCentralZero`,
  `LanglandsPrimeResonanceWitness`, `LanglandsPrimeResonanceAdmissible`,
  `LanglandsPrimeResonanceOwnerTarget`
- **S** central-zero/prime-resonance equivalences and projector transport theorems:
  `functional_equation_valid`, `sugawara_valid`,
  `central_zero_iff_L_zero`, `central_zero_of_L_zero`, `L_zero_of_central_zero`,
  `bulk_central_zero_iff_prime_resonance`, `bulk_prime_resonance_of_central_zero`,
  `bulk_central_zero_of_prime_resonance`, projector-compatibility theorems,
  witness existence theorem and owner target
- **W** explicitly non-assertive for E9, Sugawara origin, geometric Langlands, zero theorems.

## `InfoGeometry.Automorphic.HeckePurification`
- **D** `HeckeSugawaraIntertwining`
- **S** `hecke_sugawara_compatibility`, `purified_charge_eq_l_value`,
  `langlandsSugawaraBridge_nonempty_of_purification`
- **W** witness-coupled purification bridge toward Sugawara/L-function statements.

## `InfoGeometry.Arithmetic.LFunctionPotential`
- **D** `SpectralDomain`, `ScatteringLFunction`, `IsArithmeticHorizon`,
  `lFunctionPotential`, `ArithmeticBarrierDivergesAt`,
  `UnifiedHorizonWitness`
- **S** `geometric_horizon_is_arithmetic_horizon`, `arithmetic_horizon_is_geometric_horizon`,
  `geometric_horizon_iff_arithmetic_horizon`, `arithmetic_barrier_diverges_at_geometric_horizon`
- **W** conservative statement layer; exact zero-identification is witness-held.

## `InfoGeometry.Canonical.KleinBottleOrientifold`
- **D** `KleinBottleOrientifold`, `OrientifoldPrimeGasPacket`, `SquareFreeSupportPacket`
- **S** none in declarations; constructor-level/record content only.
- **W** topological interpretation and Möbius/freeness encoded as hypotheses for explicit package.

## `InfoGeometry.Canonical.ZetaTraceBridge`
- **D** `PrimeGasPartition`, `PrimeWeightSpecialization`
- **S** `zeta_trace_bridge`, `weyl_denominator_limit_eq_zeta`,
  `PrimeWeightSpecialization.partitionFunction_eq_riemannZeta`
- **W** exact bridge to existing number-theory infrastructure is theorem-safe within stated domain.

## `InfoGeometry.Canonical.BerryRotorBridge`
- **D** group/model abbreviations (`Γ`, `H`), `phaseLine`, `AbelianModularBerryData`,
  `NonAbelianSpinBerryData`, and type/class temporary scaffolding (Native Closure Mandated: Closure Debt).
- **S** `modularBerryRotor_eq_curvatureIntegral_plus_anomaly`,
  `modularBerryRotor_eq_bulkRotor_mul_anomaly`,
  `modularSpinHolonomy_eq_surfaceOrderedCurvature_mul_anomaly`
- **W** built atop cusp/cusp-limit support modules; geometric meaning is in companion layers.

## Suggested Next Use
1. Start from this surface for theorem planning:
   - direct theorems for proofs: `BilingualUpperHalfPlane`, `FiniteJonesErlangerBridge`,
     `AutomorphicKreinBridge`, `LFunctionResonance`, `ProjectedLFunction`,
     `LanglandsPrimeResonance`.
2. Use owner targets only after supplying required witness data packages.
