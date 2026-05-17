# Lean Graph Overlay / Dedup Report

## Scope

Root: `/home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Arithmetic`

## Static scan summary

- `files`: **66**
- `decls`: **1441**
- `imports`: **67**
- `edges`: **5233**
- `duplicate_alpha_classes`: **103**
- `duplicate_wl_classes`: **43**
- `sccs`: **2**
- `sorry_decl_count`: **0**
- `axiom_like_decl_count`: **0**
- `owner_target_count`: **9**
- `bridge_target_count`: **2**
- `socket_debt_count`: **21**
- `wl_rounds`: **3**

## Files

- `ArithmeticErlangenSquareRootBridge.lean` — 14 declarations
- `ArithmeticKMS.lean` — 28 declarations
- `ArithmeticSuperchargeHopfBridge.lean` — 10 declarations
- `Erdos1196ProofPin.lean` — 3 declarations
- `FinitePrimeGroverOracle.lean` — 26 declarations
- `FiniteRiemannPrimeState.lean` — 15 declarations
- `LFunctionPotential.lean` — 10 declarations
- `LFunctionRepresentationBridge.lean` — 5 declarations
- `LPrimitive.lean` — 17 declarations
- `MajoranaPolyaHilbertSocket.lean` — 99 declarations
- `MobiusDirichletInverseBridge.lean` — 3 declarations
- `MobiusDirichletInverseBridgeChecks.lean` — 0 declarations
- `MobiusFermionBosonization.lean` — 22 declarations
- `MobiusPrimonParity.lean` — 18 declarations
- `MoebiusSignature.lean` — 3 declarations
- `PrimeBitLattice.lean` — 9 declarations
- `PrimeBitWittenIndex.lean` — 18 declarations
- `PrimeBitWittenIndexChecks.lean` — 0 declarations
- `PrimeBooleanCube.lean` — 28 declarations
- `PrimeBosonFermionGas.lean` — 2 declarations
- `PrimeCantorBooleanCubeBridge.lean` — 2 declarations
- `PrimeCantorGraphDirac.lean` — 33 declarations
- `PrimeCantorLatticeDirac.lean` — 41 declarations
- `PrimeExteriorGraphDirac.lean` — 61 declarations
- `PrimeExteriorMobiusBridge.lean` — 10 declarations
- `PrimeExteriorRepresentation.lean` — 14 declarations
- `PrimeFermionSupertraceFinite.lean` — 8 declarations
- `PrimeLatticeGasVariational.lean` — 21 declarations
- `PrimeMajoranaBitFlip.lean` — 12 declarations
- `PrimeMajoranaCAR.lean` — 14 declarations
- `PrimeMajoranaOPE.lean` — 8 declarations
- `PrimeMajoranaPfaffian.lean` — 4 declarations
- `PrimeMajoranaWittenCharacter.lean` — 9 declarations
- `PrimeSpinorSquareRootBoost.lean` — 31 declarations
- `PrimeSpinorWittenIndex.lean` — 25 declarations
- `PrimeSuperalgebra.lean` — 35 declarations
- `PrimeSuperalgebraReadback.lean` — 23 declarations
- `PrimeSupertraceFinite.lean` — 42 declarations
- `PrimeVielbeinSupervolume.lean` — 8 declarations
- `PrimeWeylDenominatorBridge.lean` — 22 declarations
- `PrimeWittenCharacter.lean` — 6 declarations
- `PrimitiveBinarySuperZetaBridge.lean` — 26 declarations
- `PrimitivePrimeProjectiveTemperature.lean` — 10 declarations
- `PrimitiveProjectiveRays.lean` — 33 declarations
- `PrimitiveSetsAbove.lean` — 175 declarations
- `PrimitiveSouriauPipeline.lean` — 12 declarations
- `PrimitiveSouriauZeta.lean` — 50 declarations
- `PrimonFinite.lean` — 11 declarations
- `PrimonFreeEnergyRelativeTrace.lean` — 36 declarations
- `PrimonGasSupertrace.lean` — 13 declarations
- `PrimonKMSKreinBridge.lean` — 38 declarations
- `PrimonKreinKMS.lean` — 25 declarations
- `PrimonLiouvilleWittenIndex.lean` — 23 declarations
- `PrimonMajoranaWittenCharacter.lean` — 50 declarations
- `ProjectiveEntropy.lean` — 8 declarations
- `ProjectivePrimePartition.lean` — 7 declarations
- `ProjectiveRelativeEntropy.lean` — 19 declarations
- `ProjectiveWeylGauge.lean` — 22 declarations
- `RHQuantumStabilityBridge.lean` — 22 declarations
- `SplitMajoranaPrimeGas.lean` — 9 declarations
- `SplitMajoranaPrimon.lean` — 28 declarations
- `WeylArithmeticDivergence.lean` — 19 declarations
- `ZetaPotentialSign.lean` — 1 declarations
- `ZetaSupertraceBridge.lean` — 2 declarations
- `ZetaTraceSpecialization.lean` — 23 declarations
- `ZetaTraceVielbeinSpecialization.lean` — 20 declarations

## Alpha-normalized duplicate declaration silhouettes

### `7779c363eea6cd64` (21 declarations)
- `InfoGeometry.Arithmetic.ArithmeticSuperchargeHopfBridge.JacobiSchroedingerSpectralGate.schroedinger_valid` (theorem) in `ArithmeticSuperchargeHopfBridge.lean:133-140`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MajoranaBerryKeatingOperatorPacket.splitClifford` (theorem) in `MajoranaPolyaHilbertSocket.lean:166-172`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MajoranaBerryKeatingOperatorPacket.squareRootEnergy` (theorem) in `MajoranaPolyaHilbertSocket.lean:173-179`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MajoranaBerryKeatingOperatorPacket.dirac_square` (theorem) in `MajoranaPolyaHilbertSocket.lean:180-186`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MajoranaBerryKeatingOperatorPacket.self_adjoint` (theorem) in `MajoranaPolyaHilbertSocket.lean:187-193`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MajoranaBerryKeatingOperatorPacket.bk_mellin_sector_fixes_criticalLine` (theorem) in `MajoranaPolyaHilbertSocket.lean:194-200`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.RealMajoranaBerryKeatingProblem.combinedDirac_formula` (theorem) in `MajoranaPolyaHilbertSocket.lean:250-256`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.RealMajoranaBerryKeatingProblem.rho_anticommutes_realBK` (theorem) in `MajoranaPolyaHilbertSocket.lean:257-263`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.RealMajoranaBerryKeatingProblem.majoranaDirac_square` (theorem) in `MajoranaPolyaHilbertSocket.lean:264-270`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.RealMajoranaBerryKeatingProblem.combinedDirac_square` (theorem) in `MajoranaPolyaHilbertSocket.lean:271-277`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.FockVsMellinNormalizabilityGuard.fockSummabilityDomain` (theorem) in `MajoranaPolyaHilbertSocket.lean:312-318`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.WittenCharacterVsCompletedXiSocket.wittenCharacter_inverseZeta` (theorem) in `MajoranaPolyaHilbertSocket.lean:463-472`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.WittenCharacterVsCompletedXiSocket.spectralPfaffian_completedXi` (theorem) in `MajoranaPolyaHilbertSocket.lean:473-482`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.WittenCharacterVsCompletedXiSocket.zetaZeros_are_poles_of_inverseZeta` (theorem) in `MajoranaPolyaHilbertSocket.lean:483-492`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.ArchimedeanGammaFactorSocket.gammaFactor` (theorem) in `MajoranaPolyaHilbertSocket.lean:597-605`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.ArchimedeanGammaFactorSocket.polynomialCompletion` (theorem) in `MajoranaPolyaHilbertSocket.lean:606-614`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.CompletedXiHilbertPolyaReduction.self_adjoint` (theorem) in `MajoranaPolyaHilbertSocket.lean:805-813`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.CompletedXiHilbertPolyaReduction.renormalizedPfaffian_eq_completedXi` (theorem) in `MajoranaPolyaHilbertSocket.lean:814-822`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.CompletedXiHilbertPolyaReduction.completedXiZero` (theorem) in `MajoranaPolyaHilbertSocket.lean:823-831`
- `InfoGeometry.Arithmetic.PrimeSpinorWittenIndex.RealMajoranaWittenIndexGate.square` (theorem) in `PrimeSpinorWittenIndex.lean:267-273`
- `InfoGeometry.Arithmetic.PrimeSpinorWittenIndex.RealMajoranaWittenIndexGate.pfaffian_comparison` (theorem) in `PrimeSpinorWittenIndex.lean:274-280`

### `c38e53c19e13f756` (10 declarations)
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.BosonFermionSuperdeterminantSocket.bosonic_eq_zeta` (theorem) in `MajoranaPolyaHilbertSocket.lean:537-546`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.BosonFermionSuperdeterminantSocket.fermionic_eq_inverseZeta` (theorem) in `MajoranaPolyaHilbertSocket.lean:547-556`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.BoundaryScatteringDiscretizationSocket.boundary_or_scattering` (theorem) in `MajoranaPolyaHilbertSocket.lean:656-665`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.BoundaryScatteringDiscretizationSocket.continuous_to_spectralZeroReadout` (theorem) in `MajoranaPolyaHilbertSocket.lean:666-675`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MBKHeatTraceExplicitFormulaSocket.heatTrace_factorization` (theorem) in `MajoranaPolyaHilbertSocket.lean:719-728`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MBKHeatTraceExplicitFormulaSocket.arithmeticHeatTrace_primeSum` (theorem) in `MajoranaPolyaHilbertSocket.lean:729-738`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MBKHeatTraceExplicitFormulaSocket.bkHeatTrace_mellinContinuum` (theorem) in `MajoranaPolyaHilbertSocket.lean:739-748`
- `RelativeTraceSignatureSocket.relativeTrace_formula` (theorem) in `PrimonFreeEnergyRelativeTrace.lean:293-301`
- `RelativeTraceSignatureSocket.fermionic_primeOrbit_minusSign` (theorem) in `PrimonFreeEnergyRelativeTrace.lean:302-310`
- `MellinInversionParitySocket.log_parity` (theorem) in `PrimonFreeEnergyRelativeTrace.lean:423-432`

### `1c3f61040e32d60a` (9 declarations)
- `InfoGeometry.Arithmetic.FinitePrimeGroverOracle.QuantumCountingGate.query_bound_valid` (theorem) in `FinitePrimeGroverOracle.lean:181-187`
- `InfoGeometry.Arithmetic.FiniteRiemannPrimeState.BRSTCriticalLineGate.nilpotent` (theorem) in `FiniteRiemannPrimeState.lean:144-150`
- `InfoGeometry.Arithmetic.FiniteRiemannPrimeState.BRSTCriticalLineGate.anomaly_cancelled` (theorem) in `FiniteRiemannPrimeState.lean:151-157`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MellinPlancherelCriticalLinePacket.bk_generalizedEigenvalue` (theorem) in `MajoranaPolyaHilbertSocket.lean:62-68`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MellinPlancherelCriticalLinePacket.selfAdjoint_forces_realEigenvalue` (theorem) in `MajoranaPolyaHilbertSocket.lean:69-75`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MajoranaZeroModeNormalizabilityPacket.isZeroMode` (theorem) in `MajoranaPolyaHilbertSocket.lean:352-358`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MajoranaZeroModeNormalizabilityPacket.normalizable` (theorem) in `MajoranaPolyaHilbertSocket.lean:359-371`
- `InfoGeometry.Arithmetic.PrimeMajoranaBitFlip.PrimeMajoranaCARGate.clifford` (theorem) in `PrimeMajoranaBitFlip.lean:109-115`
- `InfoGeometry.Arithmetic.RHQuantumStabilityBridge.JacobiModularInvarianceGate.theta_transform` (theorem) in `RHQuantumStabilityBridge.lean:136-142`

### `87a99f3b3eb5c3e7` (8 declarations)
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.EssentialSelfAdjointLimitSocket.denseCore_invariant` (theorem) in `MajoranaPolyaHilbertSocket.lean:1398-1407`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.EssentialSelfAdjointLimitSocket.infiniteLimit_exists` (theorem) in `MajoranaPolyaHilbertSocket.lean:1408-1417`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.ZetaRegularizedPfaffianSocket.heatKernel_asymptotic` (theorem) in `MajoranaPolyaHilbertSocket.lean:1467-1476`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.ZetaRegularizedPfaffianSocket.finitePart_exists` (theorem) in `MajoranaPolyaHilbertSocket.lean:1477-1486`
- `InfoGeometry.Arithmetic.MobiusFermionBosonization.MobiusFermionBosonizationGate.klein_anticommutation` (theorem) in `MobiusFermionBosonization.lean:276-287`
- `InfoGeometry.Arithmetic.MobiusFermionBosonization.MobiusFermionBosonizationGate.vertex_ope` (theorem) in `MobiusFermionBosonization.lean:288-299`
- `KLEquilibriumSocket.kl_represents_freeEnergy` (theorem) in `PrimonFreeEnergyRelativeTrace.lean:477-486`
- `KLEquilibriumSocket.convexity` (theorem) in `PrimonFreeEnergyRelativeTrace.lean:487-496`

### `56ddf97e9e0abffc` (6 declarations)
- `InfoGeometry.Arithmetic.PrimeLatticeGasVariational.PrimeCountingVariationalModel.explicitFormula_valid` (theorem) in `PrimeLatticeGasVariational.lean:154-159`
- `InfoGeometry.Arithmetic.PrimeSuperalgebra.primeSuperalgebraChannel_traceLaw` (theorem) in `PrimeSuperalgebra.lean:92-102`
- `InfoGeometry.Arithmetic.PrimeSuperalgebra.squarefree_fermionic_supertrace_inverse_zeta` (theorem) in `PrimeSuperalgebra.lean:416-427`
- `InfoGeometry.Arithmetic.PrimonKMSKreinBridge.InfinitePrimonKMSCalibration.beta_admissible` (theorem) in `PrimonKMSKreinBridge.lean:318-323`
- `InfoGeometry.Arithmetic.PrimonKMSKreinBridge.InfinitePrimonKMSCalibration.partition_eq_zeta_valid` (theorem) in `PrimonKMSKreinBridge.lean:324-329`
- `InfoGeometry.Arithmetic.PrimonKMSKreinBridge.InfinitePrimonKMSCalibration.traceClassGibbs_valid` (theorem) in `PrimonKMSKreinBridge.lean:336-341`

### `5ff6a45f45716621` (6 declarations)
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.CompletedXiSuperdeterminantIdentitySocket.boson_fermion_inversion` (theorem) in `MajoranaPolyaHilbertSocket.lean:1535-1544`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.CompletedXiSuperdeterminantIdentitySocket.archimedean_completion` (theorem) in `MajoranaPolyaHilbertSocket.lean:1545-1554`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.CompletedXiSuperdeterminantIdentitySocket.superdeterminant_eq_completedXi` (theorem) in `MajoranaPolyaHilbertSocket.lean:1555-1564`
- `MobiusFreeEnergyInversionSocket.majorana_inverseZeta` (theorem) in `PrimonFreeEnergyRelativeTrace.lean:358-367`
- `MobiusFreeEnergyInversionSocket.freeEnergy_logDual` (theorem) in `PrimonFreeEnergyRelativeTrace.lean:368-377`
- `InfoGeometry.Arithmetic.RHQuantumStabilityBridge.QuantumArithmeticRHBridge.anomaly_free_critical_line` (theorem) in `RHQuantumStabilityBridge.lean:247-256`

### `939bf0d3956a301b` (5 declarations)
- `InfoGeometry.Arithmetic.ArithmeticSuperchargeHopfBridge.JacobiSchroedingerSpectralGate.density_valid` (theorem) in `ArithmeticSuperchargeHopfBridge.lean:141-155`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MajoranaBerryKeatingOperatorPacket.majorana_fock_sector_produces_pfaffianCharacter` (theorem) in `MajoranaPolyaHilbertSocket.lean:201-221`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.RealMajoranaBerryKeatingProblem.modeEnergyCoefficient_sqrtLog` (theorem) in `MajoranaPolyaHilbertSocket.lean:278-294`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.FockVsMellinNormalizabilityGuard.mellinCriticalLine` (theorem) in `MajoranaPolyaHilbertSocket.lean:319-333`
- `InfoGeometry.Arithmetic.PrimeSpinorWittenIndex.RealMajoranaWittenIndexGate.zero_mode_index` (theorem) in `PrimeSpinorWittenIndex.lean:281-291`

### `b6e76b8839d03403` (5 declarations)
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.BerryKeatingOperatorPacket.symmetrizedDilation_formula` (theorem) in `MajoranaPolyaHilbertSocket.lean:112-118`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.BerryKeatingOperatorPacket.symmetric_on_domain` (theorem) in `MajoranaPolyaHilbertSocket.lean:119-125`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MajoranaPfaffianZetaSpectralSocket.pfaffian_zeta_identity` (theorem) in `MajoranaPolyaHilbertSocket.lean:412-419`
- `InfoGeometry.Arithmetic.PrimeMajoranaBitFlip.MajoranaZeroModeGate.zero_energy` (theorem) in `PrimeMajoranaBitFlip.lean:146-152`
- `InfoGeometry.Arithmetic.PrimeSpinorSquareRootBoost.SpinLiftDoubleCoverGate.square` (theorem) in `PrimeSpinorSquareRootBoost.lean:289-295`

### `ca3f9e6b6d06439f` (5 declarations)
- `InfoGeometry.Arithmetic.FinitePrimeGroverOracle.QuantumCountingGate.counting_accuracy_valid` (theorem) in `FinitePrimeGroverOracle.lean:188-202`
- `InfoGeometry.Arithmetic.FiniteRiemannPrimeState.BRSTCriticalLineGate.critical_line` (theorem) in `FiniteRiemannPrimeState.lean:158-170`
- `InfoGeometry.Arithmetic.PrimeMajoranaBitFlip.PrimeMajoranaCARGate.bit_flip_model` (theorem) in `PrimeMajoranaBitFlip.lean:116-129`
- `InfoGeometry.Arithmetic.RHQuantumStabilityBridge.JacobiModularInvarianceGate.vacuum_modular_invariant` (theorem) in `RHQuantumStabilityBridge.lean:143-158`
- `InfoGeometry.Arithmetic.RHQuantumStabilityBridge.AnomalyFreeCriticalLineGate.critical_line_stability` (theorem) in `RHQuantumStabilityBridge.lean:172-186`

### `f6bc939379721b07` (5 declarations)
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.RelativeMBKDeterminantScatteringPacket.self_adjoint_relativeMBK` (theorem) in `MajoranaPolyaHilbertSocket.lean:1279-1290`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.RelativeMBKDeterminantScatteringPacket.relativeDeterminant_eq_completedXi` (theorem) in `MajoranaPolyaHilbertSocket.lean:1291-1302`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.RelativeMBKDeterminantScatteringPacket.scatteringTrace_eq_explicitFormula` (theorem) in `MajoranaPolyaHilbertSocket.lean:1303-1314`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.RelativeMBKDeterminantScatteringPacket.spectralShift_traceFormula` (theorem) in `MajoranaPolyaHilbertSocket.lean:1315-1326`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.RelativeMBKDeterminantScatteringPacket.completedXiZero_iff_spectralKernel` (theorem) in `MajoranaPolyaHilbertSocket.lean:1327-1343`

### `ffbd1480440ae0e4` (5 declarations)
- `InfoGeometry.Arithmetic.PrimeExteriorGraphDirac.PrimeCutoff` (abbrev) in `PrimeExteriorGraphDirac.lean:37-39`
- `InfoGeometry.Arithmetic.PrimeExteriorMobiusBridge.PrimeCutoff` (abbrev) in `PrimeExteriorMobiusBridge.lean:31-33`
- `InfoGeometry.Arithmetic.PrimeSuperalgebra.PrimeCutoff` (abbrev) in `PrimeSuperalgebra.lean:132-135`
- `InfoGeometry.Arithmetic.PrimeSuperalgebraReadback.FermionicPrimeRegister` (abbrev) in `PrimeSuperalgebraReadback.lean:41-44`
- `InfoGeometry.Arithmetic.PrimonKreinKMS.PrimeCutoff` (abbrev) in `PrimonKreinKMS.lean:40-43`

### `34bcaab1c21649dc` (4 declarations)
- `InfoGeometry.Arithmetic.FiniteRiemannPrimeState.FiniteRiemannStatePacket.normSq` (def) in `FiniteRiemannPrimeState.lean:84-87`
- `InfoGeometry.Arithmetic.PrimonGasSupertrace.FinitePrimonThermalPacket.bosonicPartition` (def) in `PrimonGasSupertrace.lean:150-153`
- `InfoGeometry.Arithmetic.PrimonGasSupertrace.FinitePrimonThermalPacket.squarefreePartition` (def) in `PrimonGasSupertrace.lean:154-157`
- `InfoGeometry.Arithmetic.PrimonGasSupertrace.FinitePrimonThermalPacket.supertrace` (def) in `PrimonGasSupertrace.lean:158-161`

### `63e92a2d0cd0c86a` (4 declarations)
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MajoranaBKTraceFormulaBridge.bosonic_zeta_channel` (theorem) in `MajoranaPolyaHilbertSocket.lean:1066-1091`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MajoranaBKTraceFormulaBridge.fermionic_inverseZeta_channel` (theorem) in `MajoranaPolyaHilbertSocket.lean:1092-1117`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MajoranaBKTraceFormulaBridge.completedZeta_archimedean_channel` (theorem) in `MajoranaPolyaHilbertSocket.lean:1118-1143`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MajoranaBKTraceFormulaBridge.boundary_scattering_spectralZero_channel` (theorem) in `MajoranaPolyaHilbertSocket.lean:1144-1169`

### `96f0a7e78301c5a7` (4 declarations)
- `InfoGeometry.Arithmetic.PrimeSuperalgebra.primeEnergy` (def) in `PrimeSuperalgebra.lean:144-147`
- `InfoGeometry.Arithmetic.PrimitiveSouriauZeta.primitiveEnergy` (def) in `PrimitiveSouriauZeta.lean:31-39`
- `InfoGeometry.Arithmetic.PrimonGasSupertrace.primonEnergy` (def) in `PrimonGasSupertrace.lean:28-31`
- `InfoGeometry.Arithmetic.PrimonMajoranaWittenCharacter.primonEnergy` (def) in `PrimonMajoranaWittenCharacter.lean:33-36`

### `cccc2d02be43b340` (4 declarations)
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.BosonFermionSuperdeterminantSocket.superdeterminant_inversion` (theorem) in `MajoranaPolyaHilbertSocket.lean:557-575`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.BoundaryScatteringDiscretizationSocket.phaseShift_matches_zetaArgument` (theorem) in `MajoranaPolyaHilbertSocket.lean:676-694`
- `RelativeTraceSignatureSocket.relativeTrace_matches_explicitFormula` (theorem) in `PrimonFreeEnergyRelativeTrace.lean:311-330`
- `MellinInversionParitySocket.functionalEquation_symmetry` (theorem) in `PrimonFreeEnergyRelativeTrace.lean:433-451`

### `d53f739137eae1f3` (4 declarations)
- `InfoGeometry.Arithmetic.finitePrimeVielbeinSupertrace` (def) in `PrimeVielbeinSupervolume.lean:33-37`
- `InfoGeometry.Arithmetic.finitePrimeVielbeinSupervolume` (def) in `PrimeVielbeinSupervolume.lean:38-47`
- `InfoGeometry.Arithmetic.ZetaTraceSpecialization.finiteZetaTraceSupertrace` (def) in `ZetaTraceSpecialization.lean:72-76`
- `InfoGeometry.Arithmetic.ZetaTraceSpecialization.finiteZetaTraceDenominator` (def) in `ZetaTraceSpecialization.lean:77-85`

### `f83e5bb325cd45da` (4 declarations)
- `InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter.equivariantRealWittenCharacter` (def) in `PrimeMajoranaWittenCharacter.lean:33-37`
- `InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter.dirichletWittenCharacterReadout` (def) in `PrimeMajoranaWittenCharacter.lean:38-42`
- `InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter.mobiusGradedThermalCharacter` (def) in `PrimeMajoranaWittenCharacter.lean:43-47`
- `InfoGeometry.Arithmetic.SplitMajoranaPrimon.stableProjectedChiralIndex` (def) in `SplitMajoranaPrimon.lean:231-235`

### `111aa850b8e4b881` (3 declarations)
- `InfoGeometry.Arithmetic.ArithmeticSuperchargeHopfBridge.HopfDifferentialGate.valid` (theorem) in `ArithmeticSuperchargeHopfBridge.lean:106-119`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.BerryKeatingOperatorPacket.self_adjoint_extension` (theorem) in `MajoranaPolyaHilbertSocket.lean:126-140`
- `InfoGeometry.Arithmetic.PrimeSpinorSquareRootBoost.SpinLiftDoubleCoverGate.projective_ratio` (theorem) in `PrimeSpinorSquareRootBoost.lean:296-312`

### `23b99f02396747cd` (3 declarations)
- `WeylMobiusDeterminantInversionSocket.determinant_inversion` (theorem) in `PrimonFreeEnergyRelativeTrace.lean:144-153`
- `WeylMobiusDeterminantInversionSocket.log_sign_flip` (theorem) in `PrimonFreeEnergyRelativeTrace.lean:154-163`
- `WeylMobiusDeterminantInversionSocket.endpoints_exchanged` (theorem) in `PrimonFreeEnergyRelativeTrace.lean:164-173`

### `53aab99f5ef2fc9a` (3 declarations)
- `InfoGeometry.Arithmetic.PrimitiveSouriauZeta.PrimitiveSouriauZetaCalibration.entropy_le_iff_weight_le` (theorem) in `PrimitiveSouriauZeta.lean:358-365`
- `InfoGeometry.Arithmetic.PrimitiveSouriauZeta.PrimitiveSouriauZetaCalibration.objective_le_iff_weight_le` (theorem) in `PrimitiveSouriauZeta.lean:366-373`
- `InfoGeometry.Arithmetic.PrimitiveSouriauZeta.PrimitiveSouriauZetaCalibration.freeEnergy_le_iff_weight_le` (theorem) in `PrimitiveSouriauZeta.lean:374-384`

### `55cfd59ad9141e96` (3 declarations)
- `InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter.primeMajoranaWittenCharacterOwnerTarget` (theorem) in `PrimeMajoranaWittenCharacter.lean:93-100`
- `InfoGeometry.Arithmetic.PrimeWittenCharacter.primeWittenCharacterOwnerTarget` (theorem) in `PrimeWittenCharacter.lean:81-88`
- `InfoGeometry.Arithmetic.PrimonMajoranaWittenCharacter.primonMajoranaWittenCharacterOwnerTarget` (theorem) in `PrimonMajoranaWittenCharacter.lean:323-330`

### `73badae45acae367` (3 declarations)
- `InfoGeometry.Arithmetic.FiniteRiemannPrimeState.HardyLittlewoodEntanglementGate` (structure) in `FiniteRiemannPrimeState.lean:106-115`
- `InfoGeometry.Arithmetic.MobiusFermionBosonization.DeterminantVandermondeComparisonGate` (structure) in `MobiusFermionBosonization.lean:228-237`
- `InfoGeometry.Arithmetic.RHQuantumStabilityBridge.TopologicalZeroSingularityGate` (structure) in `RHQuantumStabilityBridge.lean:187-196`

### `778f474b7d881126` (3 declarations)
- `InfoGeometry.Arithmetic.PrimeBooleanCube.Vertex` (abbrev) in `PrimeBooleanCube.lean:43-47`
- `InfoGeometry.Arithmetic.PrimeCantorGraphDirac.PrimeCantorVertex` (abbrev) in `PrimeCantorGraphDirac.lean:37-41`
- `InfoGeometry.Arithmetic.PrimeCantorLatticeDirac.CantorVertex` (abbrev) in `PrimeCantorLatticeDirac.lean:43-47`

### `7f28016d1e098cdd` (3 declarations)
- `InfoGeometry.Arithmetic.PrimonLiouvilleWittenIndex.oneLaneFermionicWittenIndex_eq_product` (theorem) in `PrimonLiouvilleWittenIndex.lean:53-65`
- `InfoGeometry.Arithmetic.PrimonLiouvilleWittenIndex.stableChiralIndex_eq_product` (theorem) in `PrimonLiouvilleWittenIndex.lean:73-85`
- `InfoGeometry.Arithmetic.PrimonLiouvilleWittenIndex.unstableChiralIndex_eq_product` (theorem) in `PrimonLiouvilleWittenIndex.lean:93-108`

### `99b75f137bb8c6c2` (3 declarations)
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.BosonFermionSuperdeterminantSocket` (structure) in `MajoranaPolyaHilbertSocket.lean:515-536`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.BoundaryScatteringDiscretizationSocket` (structure) in `MajoranaPolyaHilbertSocket.lean:634-655`
- `RelativeTraceSignatureSocket` (structure) in `PrimonFreeEnergyRelativeTrace.lean:270-292`

### `a8c6fc9239b4a10c` (3 declarations)
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MBKAnalyticFrontier.all_three_fronts_closed` (theorem) in `MajoranaPolyaHilbertSocket.lean:1611-1626`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MBKAnalyticFrontier.infiniteOperator_essentialSelfAdjoint` (theorem) in `MajoranaPolyaHilbertSocket.lean:1627-1642`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MBKAnalyticFrontier.regularizedPfaffian_meromorphic` (theorem) in `MajoranaPolyaHilbertSocket.lean:1643-1658`

### `b4b321c33ed0ac9c` (3 declarations)
- `InfoGeometry.Arithmetic.PrimonLiouvilleWittenIndex.StableBranchRegularization.regularized_eq_stable_branch` (theorem) in `PrimonLiouvilleWittenIndex.lean:182-186`
- `InfoGeometry.Arithmetic.PrimonLiouvilleWittenIndex.ProjectedHyperbolicChiralIndexPacket.stable_is_oneLane` (theorem) in `PrimonLiouvilleWittenIndex.lean:237-241`
- `InfoGeometry.Arithmetic.PrimonLiouvilleWittenIndex.ProjectedHyperbolicChiralIndexPacket.unstable_is_oneLane` (theorem) in `PrimonLiouvilleWittenIndex.lean:242-246`

### `cac29e88cb289e28` (3 declarations)
- `InfoGeometry.Arithmetic.FiniteRiemannPrimeState.HardyLittlewoodEntanglementGate.valid` (theorem) in `FiniteRiemannPrimeState.lean:116-130`
- `InfoGeometry.Arithmetic.MobiusFermionBosonization.DeterminantVandermondeComparisonGate.valid` (theorem) in `MobiusFermionBosonization.lean:238-253`
- `InfoGeometry.Arithmetic.RHQuantumStabilityBridge.TopologicalZeroSingularityGate.valid` (theorem) in `RHQuantumStabilityBridge.lean:197-211`

### `d16d2d402fa5bd8a` (3 declarations)
- `InfoGeometry.Arithmetic.PrimonLiouvilleWittenIndex.oneLaneFermionicWittenIndex` (def) in `PrimonLiouvilleWittenIndex.lean:41-52`
- `InfoGeometry.Arithmetic.PrimonLiouvilleWittenIndex.stableChiralIndex` (def) in `PrimonLiouvilleWittenIndex.lean:66-72`
- `InfoGeometry.Arithmetic.PrimonLiouvilleWittenIndex.unstableChiralIndex` (def) in `PrimonLiouvilleWittenIndex.lean:86-92`

### `f44b2ea5c32d856a` (3 declarations)
- `InfoGeometry.Arithmetic.PrimeMajoranaOPE.MobiusCurrentOPE.current_c_valid` (theorem) in `PrimeMajoranaOPE.lean:95-99`
- `InfoGeometry.Arithmetic.PrimeSuperalgebraReadback.PrimeDGSuperalgebraWitness.d_sq_zero_valid` (theorem) in `PrimeSuperalgebraReadback.lean:224-228`
- `InfoGeometry.Arithmetic.PrimonLiouvilleWittenIndex.StableBranchRegularization.projectStable_valid` (theorem) in `PrimonLiouvilleWittenIndex.lean:187-191`

### `ff680afcc79103fb` (3 declarations)
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.EssentialSelfAdjointLimitSocket.infiniteOperator_essentialSelfAdjoint` (theorem) in `MajoranaPolyaHilbertSocket.lean:1418-1436`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.ZetaRegularizedPfaffianSocket.regularizedPfaffian_meromorphic` (theorem) in `MajoranaPolyaHilbertSocket.lean:1487-1505`
- `KLEquilibriumSocket.equilibrium_criticalLine` (theorem) in `PrimonFreeEnergyRelativeTrace.lean:497-516`

### `01bad3512358951a` (2 declarations)
- `InfoGeometry.Arithmetic.PrimitiveSouriauZeta.identityPrimitiveSouriauZetaCalibration.entropy_eq_weight` (theorem) in `PrimitiveSouriauZeta.lean:568-579`
- `InfoGeometry.Arithmetic.PrimitiveSouriauZeta.identityPrimitiveSouriauZetaCalibration.objective_eq_weight` (theorem) in `PrimitiveSouriauZeta.lean:580-591`

### `038c22ac9d4821b1` (2 declarations)
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MajoranaPolyaHilbertBridge.selfAdjoint_spectrum_real` (theorem) in `MajoranaPolyaHilbertSocket.lean:893-904`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MajoranaPolyaHilbertBridge.zeroModes_match_zetaZeros` (theorem) in `MajoranaPolyaHilbertSocket.lean:905-921`

### `0536ebbe63625b52` (2 declarations)
- `InfoGeometry.Arithmetic.MobiusPrimonParity.finiteMajoranaChiralityCharacter_eq_mobiusGradedThermalCharacter` (theorem) in `MobiusPrimonParity.lean:130-142`
- `InfoGeometry.Arithmetic.SplitMajoranaPrimon.majoranaPfaffianProduct_eq_dirichletWittenCharacter` (theorem) in `SplitMajoranaPrimon.lean:193-202`

### `0b023d8d203c2506` (2 declarations)
- `InfoGeometry.Arithmetic.PrimeSpinorWittenIndex.finiteMajoranaPfaffianReadout` (def) in `PrimeSpinorWittenIndex.lean:169-175`
- `InfoGeometry.Arithmetic.PrimeSpinorWittenIndex.finiteMajoranaDeterminantReadout` (def) in `PrimeSpinorWittenIndex.lean:176-184`

### `14639caf6a528087` (2 declarations)
- `InfoGeometry.Arithmetic.PrimitiveSetAboveTwo` (def) in `PrimitiveSetsAbove.lean:430-434`
- `InfoGeometry.Arithmetic.PrimitiveFinsetAboveTwo` (def) in `PrimitiveSetsAbove.lean:435-441`

### `178045fec59fd189` (2 declarations)
- `InfoGeometry.Arithmetic.PrimitiveSet.mono` (theorem) in `PrimitiveSetsAbove.lean:223-231`
- `InfoGeometry.Arithmetic.PrimitiveFinset.mono` (theorem) in `PrimitiveSetsAbove.lean:232-240`

### `1d8815efb50c280f` (2 declarations)
- `InfoGeometry.Arithmetic.LPrimitiveFinset` (def) in `LPrimitive.lean:55-58`
- `InfoGeometry.Arithmetic.PrimitiveFinset` (def) in `PrimitiveSetsAbove.lean:78-81`

### `21cc53650dde8025` (2 declarations)
- `InfoGeometry.Arithmetic.PrimitiveSouriauZeta.PrimitiveSouriauZetaCalibration.freeEnergyReadout_eq_objectiveReadout` (theorem) in `PrimitiveSouriauZeta.lean:293-299`
- `InfoGeometry.Arithmetic.PrimitiveSouriauZeta.PrimitiveSouriauZetaCalibration.entropyReadout_eq_objectiveReadout` (theorem) in `PrimitiveSouriauZeta.lean:300-309`

### `23bc860a42b1f16f` (2 declarations)
- `InfoGeometry.Arithmetic.PrimonKreinKMS.finiteFermionPartition` (def) in `PrimonKreinKMS.lean:48-51`
- `InfoGeometry.Arithmetic.PrimonKreinKMS.finiteFermionSupertrace` (def) in `PrimonKreinKMS.lean:52-59`

### `2ab82be6492c462f` (2 declarations)
- `InfoGeometry.Arithmetic.PrimitiveSouriauZeta.PrimitiveSouriauZetaCalibration.entropyReadout_le_candidate_of_admissible_maxEnt` (theorem) in `PrimitiveSouriauZeta.lean:454-464`
- `InfoGeometry.Arithmetic.PrimitiveSouriauZeta.PrimitiveSouriauZetaCalibration.objectiveReadout_le_candidate_of_admissible_maxEnt` (theorem) in `PrimitiveSouriauZeta.lean:465-475`

### `2c404e86d4c73da0` (2 declarations)
- `InfoGeometry.Arithmetic.PrimeSuperalgebraReadback.PrimeSuperalgebraWitness.supercommutativity_valid` (theorem) in `PrimeSuperalgebraReadback.lean:190-202`
- `InfoGeometry.Arithmetic.PrimonLiouvilleWittenIndex.StableBranchRegularization.removesUnstableBranch_valid` (theorem) in `PrimonLiouvilleWittenIndex.lean:192-206`

### `2f314e966b637c60` (2 declarations)
- `InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge.finitePrimeWeylDenominator_eq_signedFermionPartition` (theorem) in `PrimeWeylDenominatorBridge.lean:50-58`
- `InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge.finitePrimeBosonicInverseDenominator_eq_bosonPartition` (theorem) in `PrimeWeylDenominatorBridge.lean:59-76`

### `3418cfa0397c6190` (2 declarations)
- `InfoGeometry.Arithmetic.PrimeExteriorGraphDirac.skewBlockPfaffian` (def) in `PrimeExteriorGraphDirac.lean:543-546`
- `InfoGeometry.Arithmetic.SplitMajoranaPrimon.skewBlockPfaffian` (def) in `SplitMajoranaPrimon.lean:184-187`

### `3635f791d5b19a24` (2 declarations)
- `InfoGeometry.Arithmetic.PrimeBooleanCube.majoranaFlip_subset_of_subset` (theorem) in `PrimeBooleanCube.lean:71-85`
- `InfoGeometry.Arithmetic.PrimeCantorGraphDirac.majoranaFlip_subset_of_subset` (theorem) in `PrimeCantorGraphDirac.lean:56-70`

### `37cd1245b4e2da63` (2 declarations)
- `InfoGeometry.Arithmetic.PrimeBooleanCube.occupied` (def) in `PrimeBooleanCube.lean:48-52`
- `InfoGeometry.Arithmetic.PrimeCantorGraphDirac.PrimeCantorVertex.occupied` (def) in `PrimeCantorGraphDirac.lean:42-47`

### `39446f15e3535298` (2 declarations)
- `InfoGeometry.Arithmetic.FinitePrimeGroverOracle.finiteAmplitudeNormSq` (def) in `FinitePrimeGroverOracle.lean:67-73`
- `InfoGeometry.Arithmetic.FiniteRiemannPrimeState.finiteRiemannNormSq` (def) in `FiniteRiemannPrimeState.lean:35-45`

### `3f3f1b1fb8f62e0b` (2 declarations)
- `InfoGeometry.Arithmetic.PrimeLatticeGasVariational.PrimeCountingVariationalModel.extremum_valid` (theorem) in `PrimeLatticeGasVariational.lean:160-173`
- `InfoGeometry.Arithmetic.PrimonKMSKreinBridge.InfinitePrimonKMSCalibration.positiveKMS_valid` (theorem) in `PrimonKMSKreinBridge.lean:342-354`

### `40dae18369755a1b` (2 declarations)
- `InfoGeometry.Arithmetic.PrimonKMSKreinBridge.PositiveGibbsKMSWitness.kms_valid` (theorem) in `PrimonKMSKreinBridge.lean:226-231`
- `InfoGeometry.Arithmetic.PrimonKMSKreinBridge.DoubledKreinPrimonKMSPacket.liouvilleanKreinSelfAdjoint_valid` (theorem) in `PrimonKMSKreinBridge.lean:420-425`

### `4336baa187f03598` (2 declarations)
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.EssentialSelfAdjointLimitSocket` (structure) in `MajoranaPolyaHilbertSocket.lean:1368-1397`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.ZetaRegularizedPfaffianSocket` (structure) in `MajoranaPolyaHilbertSocket.lean:1437-1466`

## WL duplicate graph neighborhoods

### `2352f387d0642ad5` (5 declarations)
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MajoranaBerryKeatingOperatorPacket.splitClifford` (theorem) in `MajoranaPolyaHilbertSocket.lean:166-172`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MajoranaBerryKeatingOperatorPacket.squareRootEnergy` (theorem) in `MajoranaPolyaHilbertSocket.lean:173-179`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MajoranaBerryKeatingOperatorPacket.dirac_square` (theorem) in `MajoranaPolyaHilbertSocket.lean:180-186`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MajoranaBerryKeatingOperatorPacket.self_adjoint` (theorem) in `MajoranaPolyaHilbertSocket.lean:187-193`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MajoranaBerryKeatingOperatorPacket.bk_mellin_sector_fixes_criticalLine` (theorem) in `MajoranaPolyaHilbertSocket.lean:194-200`

### `59f76a4082cc0ce3` (5 declarations)
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.RelativeMBKDeterminantScatteringPacket.self_adjoint_relativeMBK` (theorem) in `MajoranaPolyaHilbertSocket.lean:1279-1290`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.RelativeMBKDeterminantScatteringPacket.relativeDeterminant_eq_completedXi` (theorem) in `MajoranaPolyaHilbertSocket.lean:1291-1302`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.RelativeMBKDeterminantScatteringPacket.scatteringTrace_eq_explicitFormula` (theorem) in `MajoranaPolyaHilbertSocket.lean:1303-1314`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.RelativeMBKDeterminantScatteringPacket.spectralShift_traceFormula` (theorem) in `MajoranaPolyaHilbertSocket.lean:1315-1326`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.RelativeMBKDeterminantScatteringPacket.completedXiZero_iff_spectralKernel` (theorem) in `MajoranaPolyaHilbertSocket.lean:1327-1343`

### `4c59f7e8f17061ff` (4 declarations)
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.RealMajoranaBerryKeatingProblem.combinedDirac_formula` (theorem) in `MajoranaPolyaHilbertSocket.lean:250-256`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.RealMajoranaBerryKeatingProblem.rho_anticommutes_realBK` (theorem) in `MajoranaPolyaHilbertSocket.lean:257-263`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.RealMajoranaBerryKeatingProblem.majoranaDirac_square` (theorem) in `MajoranaPolyaHilbertSocket.lean:264-270`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.RealMajoranaBerryKeatingProblem.combinedDirac_square` (theorem) in `MajoranaPolyaHilbertSocket.lean:271-277`

### `e25ef5ad83e187f7` (4 declarations)
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MajoranaBKTraceFormulaBridge.bosonic_zeta_channel` (theorem) in `MajoranaPolyaHilbertSocket.lean:1066-1091`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MajoranaBKTraceFormulaBridge.fermionic_inverseZeta_channel` (theorem) in `MajoranaPolyaHilbertSocket.lean:1092-1117`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MajoranaBKTraceFormulaBridge.completedZeta_archimedean_channel` (theorem) in `MajoranaPolyaHilbertSocket.lean:1118-1143`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MajoranaBKTraceFormulaBridge.boundary_scattering_spectralZero_channel` (theorem) in `MajoranaPolyaHilbertSocket.lean:1144-1169`

### `1232707d5d082fac` (3 declarations)
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.CompletedXiSuperdeterminantIdentitySocket.boson_fermion_inversion` (theorem) in `MajoranaPolyaHilbertSocket.lean:1535-1544`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.CompletedXiSuperdeterminantIdentitySocket.archimedean_completion` (theorem) in `MajoranaPolyaHilbertSocket.lean:1545-1554`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.CompletedXiSuperdeterminantIdentitySocket.superdeterminant_eq_completedXi` (theorem) in `MajoranaPolyaHilbertSocket.lean:1555-1564`

### `2d8c442ca77e29f3` (3 declarations)
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.CompletedXiHilbertPolyaReduction.self_adjoint` (theorem) in `MajoranaPolyaHilbertSocket.lean:805-813`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.CompletedXiHilbertPolyaReduction.renormalizedPfaffian_eq_completedXi` (theorem) in `MajoranaPolyaHilbertSocket.lean:814-822`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.CompletedXiHilbertPolyaReduction.completedXiZero` (theorem) in `MajoranaPolyaHilbertSocket.lean:823-831`

### `2fe2f37a6d0a83c3` (3 declarations)
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MBKAnalyticFrontier.all_three_fronts_closed` (theorem) in `MajoranaPolyaHilbertSocket.lean:1611-1626`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MBKAnalyticFrontier.infiniteOperator_essentialSelfAdjoint` (theorem) in `MajoranaPolyaHilbertSocket.lean:1627-1642`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MBKAnalyticFrontier.regularizedPfaffian_meromorphic` (theorem) in `MajoranaPolyaHilbertSocket.lean:1643-1658`

### `30bea2b71db0013b` (3 declarations)
- `InfoGeometry.Arithmetic.PrimitiveSouriauZeta.PrimitiveSouriauZetaCalibration.entropy_le_iff_weight_le` (theorem) in `PrimitiveSouriauZeta.lean:358-365`
- `InfoGeometry.Arithmetic.PrimitiveSouriauZeta.PrimitiveSouriauZetaCalibration.objective_le_iff_weight_le` (theorem) in `PrimitiveSouriauZeta.lean:366-373`
- `InfoGeometry.Arithmetic.PrimitiveSouriauZeta.PrimitiveSouriauZetaCalibration.freeEnergy_le_iff_weight_le` (theorem) in `PrimitiveSouriauZeta.lean:374-384`

### `79567075bd356210` (3 declarations)
- `WeylMobiusDeterminantInversionSocket.determinant_inversion` (theorem) in `PrimonFreeEnergyRelativeTrace.lean:144-153`
- `WeylMobiusDeterminantInversionSocket.log_sign_flip` (theorem) in `PrimonFreeEnergyRelativeTrace.lean:154-163`
- `WeylMobiusDeterminantInversionSocket.endpoints_exchanged` (theorem) in `PrimonFreeEnergyRelativeTrace.lean:164-173`

### `8fe7e4b2a8795210` (3 declarations)
- `InfoGeometry.Arithmetic.PrimonKMSKreinBridge.InfinitePrimonKMSCalibration.beta_admissible` (theorem) in `PrimonKMSKreinBridge.lean:318-323`
- `InfoGeometry.Arithmetic.PrimonKMSKreinBridge.InfinitePrimonKMSCalibration.partition_eq_zeta_valid` (theorem) in `PrimonKMSKreinBridge.lean:324-329`
- `InfoGeometry.Arithmetic.PrimonKMSKreinBridge.InfinitePrimonKMSCalibration.traceClassGibbs_valid` (theorem) in `PrimonKMSKreinBridge.lean:336-341`

### `d13d1ccaecb4d6d1` (3 declarations)
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.WittenCharacterVsCompletedXiSocket.wittenCharacter_inverseZeta` (theorem) in `MajoranaPolyaHilbertSocket.lean:463-472`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.WittenCharacterVsCompletedXiSocket.spectralPfaffian_completedXi` (theorem) in `MajoranaPolyaHilbertSocket.lean:473-482`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.WittenCharacterVsCompletedXiSocket.zetaZeros_are_poles_of_inverseZeta` (theorem) in `MajoranaPolyaHilbertSocket.lean:483-492`

### `d78819196073c69d` (3 declarations)
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MBKHeatTraceExplicitFormulaSocket.heatTrace_factorization` (theorem) in `MajoranaPolyaHilbertSocket.lean:719-728`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MBKHeatTraceExplicitFormulaSocket.arithmeticHeatTrace_primeSum` (theorem) in `MajoranaPolyaHilbertSocket.lean:729-738`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MBKHeatTraceExplicitFormulaSocket.bkHeatTrace_mellinContinuum` (theorem) in `MajoranaPolyaHilbertSocket.lean:739-748`

### `0ce559bb3049c7d6` (2 declarations)
- `InfoGeometry.Arithmetic.PrimitiveSouriauZeta.PrimitiveSouriauZetaCalibration.freeEnergyReadout_eq_objectiveReadout` (theorem) in `PrimitiveSouriauZeta.lean:293-299`
- `InfoGeometry.Arithmetic.PrimitiveSouriauZeta.PrimitiveSouriauZetaCalibration.entropyReadout_eq_objectiveReadout` (theorem) in `PrimitiveSouriauZeta.lean:300-309`

### `1504945bc1947e9b` (2 declarations)
- `KLEquilibriumSocket.kl_represents_freeEnergy` (theorem) in `PrimonFreeEnergyRelativeTrace.lean:477-486`
- `KLEquilibriumSocket.convexity` (theorem) in `PrimonFreeEnergyRelativeTrace.lean:487-496`

### `189d19a2b4618a68` (2 declarations)
- `InfoGeometry.Arithmetic.PrimitiveSouriauZeta.PrimitiveSouriauZetaCalibration.entropy_eq_integral_partitionReadout` (theorem) in `PrimitiveSouriauZeta.lean:310-329`
- `InfoGeometry.Arithmetic.PrimitiveSouriauZeta.PrimitiveSouriauZetaCalibration.objective_eq_integral_partitionReadout` (theorem) in `PrimitiveSouriauZeta.lean:330-349`

### `1ae0dda06295d1fb` (2 declarations)
- `InfoGeometry.Arithmetic.PrimitiveSouriauZeta.identityPrimitiveSouriauZetaCalibration.entropy_eq_weight` (theorem) in `PrimitiveSouriauZeta.lean:568-579`
- `InfoGeometry.Arithmetic.PrimitiveSouriauZeta.identityPrimitiveSouriauZetaCalibration.objective_eq_weight` (theorem) in `PrimitiveSouriauZeta.lean:580-591`

### `2171a7757680a9e8` (2 declarations)
- `InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter.equivariantRealWittenCharacter` (def) in `PrimeMajoranaWittenCharacter.lean:33-37`
- `InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter.dirichletWittenCharacterReadout` (def) in `PrimeMajoranaWittenCharacter.lean:38-42`

### `2230a7135996d68d` (2 declarations)
- `StableUnstableGibbsChartSocket.stable_gibbs_minimizer` (theorem) in `PrimonFreeEnergyRelativeTrace.lean:228-237`
- `StableUnstableGibbsChartSocket.inverted_chart` (theorem) in `PrimonFreeEnergyRelativeTrace.lean:238-247`

### `248143a4eed8bea8` (2 declarations)
- `InfoGeometry.Arithmetic.FiniteRiemannPrimeState.BRSTCriticalLineGate.nilpotent` (theorem) in `FiniteRiemannPrimeState.lean:144-150`
- `InfoGeometry.Arithmetic.FiniteRiemannPrimeState.BRSTCriticalLineGate.anomaly_cancelled` (theorem) in `FiniteRiemannPrimeState.lean:151-157`

### `2a4ff69f37a7b70c` (2 declarations)
- `InfoGeometry.Arithmetic.PrimitiveSouriauZeta.PrimitiveSouriauZetaCalibration.entropyReadout_le_candidate_of_maxEnt` (theorem) in `PrimitiveSouriauZeta.lean:385-399`
- `InfoGeometry.Arithmetic.PrimitiveSouriauZeta.PrimitiveSouriauZetaCalibration.objectiveReadout_le_candidate_of_maxEnt` (theorem) in `PrimitiveSouriauZeta.lean:400-411`

### `2c6ea6096be2472f` (2 declarations)
- `InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter.equivariantRealWittenCharacter_eq_eulerProduct` (theorem) in `PrimeMajoranaWittenCharacter.lean:48-54`
- `InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter.dirichletWittenCharacterReadout_eq_eulerProduct` (theorem) in `PrimeMajoranaWittenCharacter.lean:55-61`

### `3762ca9bdc0817a7` (2 declarations)
- `InfoGeometry.Arithmetic.PrimitiveSouriauZeta.PrimitiveSouriauZetaCalibration.entropy_le_candidate_of_admissible_maxEnt` (theorem) in `PrimitiveSouriauZeta.lean:476-488`
- `InfoGeometry.Arithmetic.PrimitiveSouriauZeta.PrimitiveSouriauZetaCalibration.objective_le_candidate_of_admissible_maxEnt` (theorem) in `PrimitiveSouriauZeta.lean:489-500`

### `37fd83fcbb40284d` (2 declarations)
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.ZetaRegularizedPfaffianSocket.heatKernel_asymptotic` (theorem) in `MajoranaPolyaHilbertSocket.lean:1467-1476`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.ZetaRegularizedPfaffianSocket.finitePart_exists` (theorem) in `MajoranaPolyaHilbertSocket.lean:1477-1486`

### `3c256386ff6606cb` (2 declarations)
- `InfoGeometry.Arithmetic.PrimitiveSouriauZeta.PrimitiveSouriauZetaCalibration.entropy_eq_primitiveWeightSum` (theorem) in `PrimitiveSouriauZeta.lean:273-285`
- `InfoGeometry.Arithmetic.PrimitiveSouriauZeta.PrimitiveSouriauZetaCalibration.freeEnergy_eq_primitiveWeightSum` (theorem) in `PrimitiveSouriauZeta.lean:286-292`

### `4054121cfde7aa21` (2 declarations)
- `InfoGeometry.Arithmetic.finitePrimeVielbeinSupertrace` (def) in `PrimeVielbeinSupervolume.lean:33-37`
- `InfoGeometry.Arithmetic.finitePrimeVielbeinSupervolume` (def) in `PrimeVielbeinSupervolume.lean:38-47`

### `470087f88ef2cef9` (2 declarations)
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.BerryKeatingOperatorPacket.symmetrizedDilation_formula` (theorem) in `MajoranaPolyaHilbertSocket.lean:112-118`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.BerryKeatingOperatorPacket.symmetric_on_domain` (theorem) in `MajoranaPolyaHilbertSocket.lean:119-125`

### `498a7321a11bcffc` (2 declarations)
- `InfoGeometry.Arithmetic.PrimonLiouvilleWittenIndex.StableBranchRegularization.regularized_eq_stable_branch` (theorem) in `PrimonLiouvilleWittenIndex.lean:182-186`
- `InfoGeometry.Arithmetic.PrimonLiouvilleWittenIndex.ProjectedHyperbolicChiralIndexPacket.stable_is_oneLane` (theorem) in `PrimonLiouvilleWittenIndex.lean:237-241`

### `4e6741ed00c06d70` (2 declarations)
- `RelativeTraceSignatureSocket.relativeTrace_formula` (theorem) in `PrimonFreeEnergyRelativeTrace.lean:293-301`
- `RelativeTraceSignatureSocket.fermionic_primeOrbit_minusSign` (theorem) in `PrimonFreeEnergyRelativeTrace.lean:302-310`

### `52cefe167e5686ed` (2 declarations)
- `InfoGeometry.Arithmetic.PrimitiveSouriauZeta.PrimitiveSouriauZetaCalibration.entropy_le_candidate_of_maxEnt` (theorem) in `PrimitiveSouriauZeta.lean:412-425`
- `InfoGeometry.Arithmetic.PrimitiveSouriauZeta.PrimitiveSouriauZetaCalibration.objective_le_candidate_of_maxEnt` (theorem) in `PrimitiveSouriauZeta.lean:426-441`

### `5fb4c901a32656bc` (2 declarations)
- `InfoGeometry.Arithmetic.PrimeSupertraceFinite.evenPartition` (def) in `PrimeSupertraceFinite.lean:221-227`
- `InfoGeometry.Arithmetic.PrimeSupertraceFinite.oddPartition` (def) in `PrimeSupertraceFinite.lean:228-234`

### `6aac7c771004d0ed` (2 declarations)
- `InfoGeometry.Arithmetic.PrimeMajoranaOPE.SplitMajoranaOPE.cc_valid` (theorem) in `PrimeMajoranaOPE.lean:54-59`
- `InfoGeometry.Arithmetic.PrimeMajoranaOPE.SplitMajoranaOPE.dd_valid` (theorem) in `PrimeMajoranaOPE.lean:60-65`

### `720da357fecd94f7` (2 declarations)
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.ArchimedeanGammaFactorSocket.gammaFactor` (theorem) in `MajoranaPolyaHilbertSocket.lean:597-605`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.ArchimedeanGammaFactorSocket.polynomialCompletion` (theorem) in `MajoranaPolyaHilbertSocket.lean:606-614`

### `7bcd7a432d264969` (2 declarations)
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.EssentialSelfAdjointLimitSocket.denseCore_invariant` (theorem) in `MajoranaPolyaHilbertSocket.lean:1398-1407`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.EssentialSelfAdjointLimitSocket.infiniteLimit_exists` (theorem) in `MajoranaPolyaHilbertSocket.lean:1408-1417`

### `8b9468f16961dfce` (2 declarations)
- `InfoGeometry.Arithmetic.PrimeSpinorWittenIndex.RealMajoranaWittenIndexGate.square` (theorem) in `PrimeSpinorWittenIndex.lean:267-273`
- `InfoGeometry.Arithmetic.PrimeSpinorWittenIndex.RealMajoranaWittenIndexGate.pfaffian_comparison` (theorem) in `PrimeSpinorWittenIndex.lean:274-280`

### `9c032cad3d6fadc9` (2 declarations)
- `InfoGeometry.Arithmetic.PrimitiveSouriauZeta.PrimitiveSouriauZetaCalibration.objective_eq_integral_partitionReadout_of_admissible` (theorem) in `PrimitiveSouriauZeta.lean:512-518`
- `InfoGeometry.Arithmetic.PrimitiveSouriauZeta.PrimitiveSouriauZetaCalibration.freeEnergy_eq_integral_partitionReadout_of_admissible` (theorem) in `PrimitiveSouriauZeta.lean:519-525`

### `a4e87815582e6a83` (2 declarations)
- `InfoGeometry.Arithmetic.MobiusFermionBosonization.MobiusFermionBosonizationGate.klein_anticommutation` (theorem) in `MobiusFermionBosonization.lean:276-287`
- `InfoGeometry.Arithmetic.MobiusFermionBosonization.MobiusFermionBosonizationGate.vertex_ope` (theorem) in `MobiusFermionBosonization.lean:288-299`

### `aab51b108fa0bbe0` (2 declarations)
- `PrimonFreeEnergyRelativeTraceManifest.relativeTrace_matches_explicitFormula` (theorem) in `PrimonFreeEnergyRelativeTrace.lean:595-613`
- `PrimonFreeEnergyRelativeTraceManifest.freeEnergy_logDual` (theorem) in `PrimonFreeEnergyRelativeTrace.lean:614-632`

### `ac86076f6ec46e8c` (2 declarations)
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MellinPlancherelCriticalLinePacket.bk_generalizedEigenvalue` (theorem) in `MajoranaPolyaHilbertSocket.lean:62-68`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MellinPlancherelCriticalLinePacket.selfAdjoint_forces_realEigenvalue` (theorem) in `MajoranaPolyaHilbertSocket.lean:69-75`

### `aded9350dadf1a52` (2 declarations)
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MajoranaPolyaHilbertBridge.selfAdjoint_spectrum_real` (theorem) in `MajoranaPolyaHilbertSocket.lean:893-904`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.MajoranaPolyaHilbertBridge.zeroModes_match_zetaZeros` (theorem) in `MajoranaPolyaHilbertSocket.lean:905-921`

### `b9573d466b04d8fd` (2 declarations)
- `InfoGeometry.Arithmetic.PrimitiveSouriauZeta.PrimitiveSouriauZetaCalibration.entropyReadout_le_candidate_of_admissible_maxEnt` (theorem) in `PrimitiveSouriauZeta.lean:454-464`
- `InfoGeometry.Arithmetic.PrimitiveSouriauZeta.PrimitiveSouriauZetaCalibration.objectiveReadout_le_candidate_of_admissible_maxEnt` (theorem) in `PrimitiveSouriauZeta.lean:465-475`

### `c0ef1bbc06ca732e` (2 declarations)
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.BosonFermionSuperdeterminantSocket.bosonic_eq_zeta` (theorem) in `MajoranaPolyaHilbertSocket.lean:537-546`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.BosonFermionSuperdeterminantSocket.fermionic_eq_inverseZeta` (theorem) in `MajoranaPolyaHilbertSocket.lean:547-556`

### `c71eb30f9ace0312` (2 declarations)
- `MobiusFreeEnergyInversionSocket.majorana_inverseZeta` (theorem) in `PrimonFreeEnergyRelativeTrace.lean:358-367`
- `MobiusFreeEnergyInversionSocket.freeEnergy_logDual` (theorem) in `PrimonFreeEnergyRelativeTrace.lean:368-377`

### `f69e55af867e7b00` (2 declarations)
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.BoundaryScatteringDiscretizationSocket.boundary_or_scattering` (theorem) in `MajoranaPolyaHilbertSocket.lean:656-665`
- `InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket.BoundaryScatteringDiscretizationSocket.continuous_to_spectralZeroReadout` (theorem) in `MajoranaPolyaHilbertSocket.lean:666-675`

## Strongly connected components in lexical declaration graph

- InfoGeometry.Arithmetic.PrimeLatticeGasVariational.selectedSigma_eq_half, InfoGeometry.Arithmetic.PrimeLatticeGasVariational.VariationalCriticalLineGate
- InfoGeometry.Arithmetic.ProjectiveRelativeEntropy.IntegratedProjectiveKLWitness.integratedKL_pos_of_ne_reference, InfoGeometry.Arithmetic.ProjectiveRelativeEntropy.ProjectiveKLCalibration.integrated_pos_of_ne_reference, InfoGeometry.Arithmetic.ProjectiveRelativeEntropy.IntegratedProjectiveKLWitness, InfoGeometry.Arithmetic.ProjectiveRelativeEntropy.ProjectiveKLCalibration

## Interpretation

This report is a static observability overlay. It is not a Lean proof check and not a kernel-accurate expression hash. The next precision step is a Lean-native exporter over elaborated `Expr`, using de-Bruijn indices and universe normalization, feeding this same JSON schema.