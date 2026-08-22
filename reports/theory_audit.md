# Theory Audit Report

Generated: 2026-08-22 08:08:19Z

## Build toolchain status
- lake: available (/home/goutev/.elan/bin/lake)
```bash
Lake version 5.0.0-src+978f81d (Lean version 4.28.1)
```

## Placeholder proof debt (sorry/admit)

```text
lean/InfoGeometry/InformationGeometry/ItakuraSaitoBregmanBridge.lean:16:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/InformationGeometry/BKMBipartiteTensor.lean:26:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/InformationGeometry/BKMMetricModularBridge.lean:21:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/InformationGeometry/KMSThermodynamicIdentity.lean:20:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/InformationGeometry/ArakiDonaldVariational.lean:24:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/InformationGeometry/BurgSteinSelfConcordance.lean:17:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Continuous/DeRhamUnifiedCorridor.lean:36:All theorems are 100% kernel-checked in native Mathlib 4 with zero `sorry`s.
lean/InfoGeometry/Continuous/PositiveOrthant.lean:30:All proofs are complete in native Mathlib 4 with zero `sorry`s.
lean/InfoGeometry/Continuous/Exactness.lean:26:All proofs are complete in native Mathlib 4 with zero `sorry`s.
lean/sandbox/GoldenMeanShift.lean:22:NO `sorry`, NO `axiom`, NO `admit`. Every line is kernel-checked.
lean/DAG/InfoTreeExtract.lean:216:          isSorrySourceScan := refs.contains "sorryAx" || refs.contains "sorry"
lean/DAG/FunctionalGaussJordan.lean:17:All proofs are standard linear algebra — no axioms, no sorry debt.
lean/DAG/DisconnectedAudit.lean:25:--   3. sorry_incomplete   : proof uses sorry (debt, not fake root)
lean/DAG/DisconnectedAudit.lean:95:/-- Check if a declaration's proof uses sorry. -/
lean/DAG/DisconnectedAudit.lean:104:      all.any (fun r => r.toString == "sorryAx" || r.toString == "sorry")
lean/DAG/DisconnectedAudit.lean:107:/-- Collect axiom/sorry names from a declaration. -/
lean/DAG/DisconnectedAudit.lean:119:          axioms := axioms.push s!"sorry:{n.toString}"
lean/DAG/DisconnectedAudit.lean:415:    lines := lines.push "These capstones use `sorry` in their proofs. The statements might be true"
lean/DAG/EckmannHodge.lean:12:All `sorry` debt is closed. Every theorem is a genuine algebraic proof.
lean/Agent/CompilerBridgeCore.lean:705:    s!"Declaration '{declName}' contains `sorry`."
lean/InfoGeometry/Physics/SplitOctonionDerivationSpinRep.lean:24:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Physics/OperatorCoefficientZornBdGBridge.lean:43:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Lint/NonTriviality.lean:27:* transitive ax!om audit using `Lean.collectAxioms`, with explicit `sorry` treated as honest closure debt when configured;
lean/InfoGeometry/Lint/NonTriviality.lean:57:/-- Permit explicit `sorry` as honest, visible closure debt. -/
lean/InfoGeometry/Lint/Pauli.lean:11:/-- Option to control the Pauli sorry linter. -/
lean/InfoGeometry/Lint/Pauli.lean:100:                  logError m!"[Pauli/Axiom-Surface Seal] {declName} depends on nonstandard `admitAx`; use explicit `sorry` instead of a disguised placeholder."
lean/InfoGeometry/Physics/ZornBdGDerivationBridge.lean:12:All lemmas and theorems are proven natively in Mathlib with zero `sorry`s.
lean/InfoGeometry/NCG/DualExponentialTrifoldBridge.lean:34:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/NCG/NoncommutativeCyclicCocycle.lean:20:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/NCG/CategoricalInductiveColimitKMSBridge.lean:25:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Combinatorics/BinaryPCGolayBridge.lean:37:All proofs are complete native Mathlib 4 with zero `sorry`s, zero placeholders, and zero custom axioms.
lean/InfoGeometry/NCG/NoncommutativeDifferentialCalculus.lean:18:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/NCG/NoncommutativeNoetherPoisson.lean:20:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/NCG/NoncommutativeOperatorMonotoneMetric.lean:22:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/NCG/CategoricalColimitStateDescent.lean:23:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/Omega/SPG/ErrorThreshold.lean:157:    exponent ratios `r` and `p^2 r` admit overlapping admissible observation intervals, and
lean/InfoGeometry/Physics/SplitG2SL3ModuleDecomposition.lean:27:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Clifford/FanoOctonionParavector.lean:12:All proofs are native and closed without sorry.
lean/InfoGeometry/Physics/ZornBdGSuperconductingExponentialBridge.lean:30:All theorems are proved natively in Lean 4 with Mathlib, with zero `sorry`s and zero custom axioms.
lean/Omega/GU/TerminalWindow6FiniteCompletenessTemplate.lean:27:force unique labeling, and finite audit triples admit a direct equality decision procedure.
lean/InfoGeometry/Application/OperatorFreudenthalBoundary.lean:167:  /-- Boundary states sorry Drazin surgery. -/
lean/InfoGeometry/Clifford/ConformalReflection55.lean:36:These are **native Lean proofs** — no axioms, sorry, or external certificates.
lean/Omega/EA/Sync10ResetDepthSpectrum.lean:166:other eight target states already admit depth-`5` reset words.
lean/InfoGeometry/LogarithmicBridge.lean:35:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/SelfReference/Shadow.lean:64:| ShadowKind.sorryDebt => "explicit sorry in proof body"
lean/Omega/GU/Window6Affine2FlatRootSliceSelection.lean:38:The three affine-`2`-flat cyclic words admit an explicit lookup against three `B₃` roots in the
lean/Omega/EA/PrimeRegisterOrbitFiberCoincidence.lean:9:/-- Two prime-register states lie in the same local Fibonacci orbit when they admit a common
lean/Omega/GU/JoukowskyAreaPreservingCayley.lean:22:/-- The normalized semiaxes are reciprocal and admit the usual hyperbolic parametrization. -/
lean/InfoGeometry/Lie/SO55MatrixLieSubalgebra.lean:23:are mechanically verified in Lean 4 with ZERO `sorry`s and ZERO custom axioms.
lean/InfoGeometry/Lie/CartanKreinNeutralSignatureBridge.lean:25:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Lie/G2CartanSymmetricSpaceIdentification.lean:23:and previously verified lemmas. No `sorry`, no wrappers.
lean/InfoGeometry/Architecture/CartanCosetManifold.lean:19:All proofs are complete in native Lean 4 with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Lie/SplitG2SL3ModuleDecomposition.lean:23:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Architecture/MatrixSymmetricConeFisherRao.lean:19:   proven natively with zero `sorry`s using the cyclic property of the matrix trace.
lean/InfoGeometry/Architecture/MatrixSymmetricConeFisherRao.lean:24:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/Omega/EA/RewriteCore.lean:119:/-- Any two one-step reducts admit a common normal-form descendant. -/
lean/Omega/EA/RewriteCore.lean:126:/-- Any two reducts admit a common normal-form descendant. -/
lean/InfoGeometry/Architecture/CartanGeodesicSymmetry.lean:27:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/Omega/SyncKernelWeighted/GmModqRecursionClosure.lean:14:/-- The mod-`q` residue counts admit a finite matrix-coefficient presentation.
lean/InfoGeometry/Arithmetic/PolyaHilbertDiracHodgeCantorBridge.lean:19:Plus the internal proof: `SouriauDiracHodgeCoupling` (659 lines, 32 thm, 0 sorry).
lean/InfoGeometry/Arithmetic/LagariasMontagueParityLadderBridge.lean:16:All proofs are native Mathlib with 0 `sorry`s and 0 custom axioms.
lean/InfoGeometry/Topology/SymbolicLatentObservedPathImageCompHausEvaluation.lean:10:inclusion maps sorry a genuine `CompHaus` source/target packaging.  The
lean/InfoGeometry/Modular/SemidirectExteriorAlgebra.lean:15:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/CommutantSemidirectProduct.lean:16:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/DualExponentialCommutatorBridge.lean:15:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/EntropyMonotonicity.lean:17:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/QuantumDataProcessingInequality.lean:27:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/GKSLDissipatorAlgebraic.lean:18:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/SelfConcordantBarrierTriple.lean:25:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/SemidirectAutomorphismGroup.lean:26:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/WeylPfaffianDeterminantTriple.lean:19:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/ConcreteOperatorModularBridge.lean:17:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/QuantumRelativeEntropyMonotonicity.lean:20:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/TrifoldClassification.lean:12:characterization with zero `sorry`s in native Mathlib.
lean/InfoGeometry/Modular/Noncommutative.lean:24:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/OperatorKMSThermodynamicIdentity.lean:25:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/KMSColimitExtension.lean:24:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/Omega/UnitCirclePhaseArithmetic/AppHorizonEulerPatch.lean:29:`|w| ≤ r < 1/3` the Euler terms admit a uniform geometric majorant. -/
lean/InfoGeometry/Modular/ModularCocycleKMSBridge.lean:49:All proofs are complete in native Mathlib 4 with zero `sorry`s, zero wrappers, and zero custom axioms.
lean/InfoGeometry/Lie/CartanCosetRiemannCurvatureBridge.lean:26:All proofs are native Lean 4 with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/InnerDerivationLieIdeal.lean:18:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/ZetaRegularizedDeterminantBridge.lean:20:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/ModularTimeSemigroupBridge.lean:19:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/DualExponentialBerezinianAutomorphismBridge.lean:21:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/TrifoldRadonNikodymBridge.lean:17:All proofs are complete in native Mathlib with zero `sorry`s.
lean/InfoGeometry/Modular/SchrodingerGKSL.lean:20:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Topology/CompletedZetaV4CharacterBridge.lean:28:All proofs are 100% genuine Lean 4 proofs with 0 `sorry` and 0 custom axioms.
lean/InfoGeometry/Arithmetic/ZetaDihedral.lean:15:No deferred interfaces. No certificates. No axioms. No `sorry`.
lean/InfoGeometry/Arithmetic/ChebyshevPrimeEnergyBound.lean:25:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Arithmetic/SelfConcordantZetaBarrierProofs.lean:6:No deferred interfaces. No certificates. No axioms. No `sorry`.
lean/InfoGeometry/Lie/SouriauBregmanDualityBridge.lean:17:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Automorphic/HeckePurification.lean:82:  `Prop`/`sorry` placeholder with a concrete theorem-shaped obligation.
lean/InfoGeometry/Lie/G2TwoRealSplitClassification.lean:38:no `sorry`, no external enumeration is invoked inside this file itself.
lean/InfoGeometry/LLM/AttentionEntropyProductionFlow.lean:27:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Topology/MobiusDeRhamMonodromy.lean:29:## Verified theorems (no sorry)
lean/InfoGeometry/Topology/SymbolicLatentVaryingCarrierQuotientCompHausLimit.lean:8:and observation-range diagrams sorry genuine `CompHaus` limits.  This owner
lean/Omega/POM/OracleCapacityKolmogorovSpectrum.lean:12:points in the fiber over `x` admit a description of length at most `B`, while `fiberContainment`
lean/InfoGeometry/OperatorAlgebra/SplitQuaternionSL2Isomorphism.lean:20:All proofs are native Lean 4 derivations checked by the kernel with zero remaining sorry debt.
lean/InfoGeometry/Analysis/LogDetSelfConcordantBarrier.lean:21:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/Omega/Zeta/RealInput40GeodesicRamanujanMargin.lean:41:gap exponent is `log (λ_nb² / ρ_nb)`, and both the primitive-orbit and prime-orbit counts admit
lean/InfoGeometry/OperatorAlgebra/ChiralRailPlane.lean:19:All relations are verified with native Mathlib proofs and zero `sorry`s.
lean/InfoGeometry/Lie/SplitOctonionDerivationSpinRep.lean:16:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/OperatorAlgebra/SplitOctonionLoxodromic.lean:18:All proofs are native Lean 4 derivations checked by the kernel with zero remaining sorry debt.
lean/Omega/Zeta/XiToeplitzDetVerblunsky.lean:119:/-- Paper label: `thm:xi-toeplitz-det-verblunsky`. The Toeplitz determinants admit the exact
lean/Omega/POM/FractranPermutationEmbeddingLength.lean:52:/-- Finite permutations admit a prime-encoded FRACTRAN realization, and any program carrying a
lean/InfoGeometry/Analysis/AsanoRuelleBasicBranches.lean:16:No `sorry`.
lean/InfoGeometry/Projective/SplitOctonions/SplitOctonionsLegendre.lean:21:No wrappers. No `sorry`.
lean/InfoGeometry/Projective/SplitOctonions/SplitOctonionsColorStabilizer.lean:14:No wrappers. No `sorry`.
lean/InfoGeometry/Projective/SplitOctonions/ProjectivePolarInvariant.lean:21:No `sorry`.
lean/InfoGeometry/Projective/SplitOctonions/BektasMatrix.lean:14:No wrappers. No `sorry`.
lean/InfoGeometry/Projective/SplitOctonions/ProjectivePolarFiberTransport.lean:22:No `sorry`.
lean/InfoGeometry/Projective/SplitOctonions/ProjectivePolarFiber.lean:19:No `sorry`.
lean/InfoGeometry/Analysis/LaplaceUniqueness.lean:302:If two Laplace data agree on the same Bromwich contour and both sorry the
lean/InfoGeometry/QuantumGeometry/KreinToHilbertCartanBridge.lean:28:All proofs are native Mathlib 4 derivations checked by the kernel with zero `sorry`s.
lean/InfoGeometry/QuantumGeometry/KahlerSouriauInformationBridge.lean:22:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Projective/KleinQuadricPlucker.lean:16:No wrappers. No `sorry`.
lean/InfoGeometry/QuantumGeometry/Unification.lean:15:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/QuantumGeometry/TangentCotangentSymplecticBridge.lean:15:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Projective/KleinCrossRatioInvariant.lean:16:No wrappers. No `sorry`.
lean/InfoGeometry/QuantumGeometry/BerryKeatingDilationBridge.lean:34:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/OperatorAlgebra/OperatorExteriorAlgebraGeneral.lean:18:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/QuantumGeometry/TensorBridge.lean:20:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Projective/SplitOctonions.lean:16:No `sorry`, no `True` placeholders, no fake Freudenthal determinant.
lean/InfoGeometry/Topology/CliffordMobiusDeRhamMonodromy.lean:23:## Verified theorems (no sorry)
lean/InfoGeometry/Synthesis/OnsagerOperatorDifferentialCalculus.lean:18:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Projective/KleinQuadric.lean:23:No `sorry`.
lean/InfoGeometry/Probability/ExpLogRNDerivation.lean:45:All proofs are 100% native Mathlib with zero `sorry`s, zero placeholders, and zero custom axioms.
lean/InfoGeometry/Projective/KleinQuadricIncidence.lean:16:No wrappers. No `sorry`.
lean/InfoGeometry/Probability/HomologicalProbability.lean:838:Type III von Neumann factors sorry no finite normal tracial state.
lean/InfoGeometry/Tooling/VacuityCritic.lean:24:    field.value != "sorry" && field.value != "sorry"
lean/InfoGeometry/OperatorAlgebra/SplitOctonionPseudoReal.lean:18:No `sorry`/`ax!om`/`sorry`/property scaffolding is used.
lean/InfoGeometry/Projective/Quadrics/AffineSlices.lean:23:No `sorry`.
lean/InfoGeometry/OperatorAlgebra/ChiralCliffordSplit.lean:17:All proofs are native, formal Lean 4 derivations checked by the kernel with zero sorry debt.
lean/InfoGeometry/OperatorAlgebra/TripotentMatrix2x2.lean:15:All proofs are native Lean 4 derivations checked by the kernel with zero remaining sorry debt.
lean/InfoGeometry/Topology/WeierstrassHadamardDivisorBridge.lean:30:All proofs are 100% native in Lean 4 with 0 `sorry` and 0 custom axioms.
lean/Omega/Zeta/XiOffcriticalDichotomyAcceptableOrNull.lean:14:/-- Off-critical claims either admit the explicit acceptable radial extension with the sharp
lean/InfoGeometry/OperatorAlgebra/WittenMöbiusBraidBridge.lean:18:All proofs are native Lean 4 derivations checked by the kernel with zero remaining sorry debt.
lean/InfoGeometry/Topology/XiHardyZNormalizationBridge.lean:28:All proofs are 100% genuine Lean 4 proofs with 0 `sorry` and 0 custom axioms.
lean/InfoGeometry/AsanoRuelle/MobiusInversion.lean:9:No placeholders. No `sorry`.
lean/InfoGeometry/Information/SouriauLieGroupThermodynamics.lean:35:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/AsanoRuelle/AsanoRuelleCounterexample.lean:12:No wrappers. No `sorry`.
lean/InfoGeometry/Information/ModularCocycleKMSBridge.lean:37:All proofs are 100% native Mathlib with zero `sorry`s, zero placeholders, and zero custom axioms.
lean/InfoGeometry/Information/MasterArchetypeConvexDuality.lean:42:All theorems are fully proved with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Information/UniversalDualityQuadrangle.lean:29:All theorems are fully proved in native Mathlib with zero `sorry`s and zero custom axioms.
lean/Omega/Zeta/XiPrimeRegisterHistoryInverseLimit.lean:118:/-- Finite-history register prefixes admit injective recursive encodings, and the compatible tower
lean/InfoGeometry/External/Auto/BlackHoleHolography.lean:10:the scalar entropy algebra below is proved without axioms or `sorry`.
lean/Omega/Folding/FiberIdentifiableSigmaAlgebraMaximal.lean:8:admit an explicit inverse kernel whose translated pattern counts are read off from the subset
lean/InfoGeometry/Algebra/ExplogRN.lean:19:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Algebra/AssociativityObstruction.lean:31:* therefore a genuinely nonassociative algebra cannot sorry such a
lean/Omega/Zeta/DerivedZGHardcoreFactorization.lean:59:Euler factors admit the `ζ(σ) / ζ(2σ)` local rewrite, the finite-support sequence stabilizes, and
lean/InfoGeometry/Topology/NativeMathlibZetaMetriplecticFlowBridge.lean:16:- ZERO `sorry`
lean/InfoGeometry/Algebra/NilpotentNonunit.lean:11:No wrappers. No `sorry`.
lean/InfoGeometry/Algebra/ZeckendorfBijection.lean:15:NO `sorry`, NO `ax!om`, NO `sorry`. Every line is kernel-checked.
lean/InfoGeometry/Algebra/CuntzRecursiveFermionSystem.lean:219:/-! ## Wedge Actions (sorry-free) -/
lean/Omega/Zeta/XiWindow6MinrepZeckendorfSignatureInjection.lean:47:The `21` minimal reachable representatives admit explicit Zeckendorf signatures; each evaluates to
lean/InfoGeometry/Algebra/NonAssocPeirceFrame.lean:26:All proofs are 100% native Mathlib with zero `sorry`s, zero custom axioms, and zero admits.
lean/InfoGeometry/Algebra/GogberashviliNilpotentCARBridge.lean:20:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/Omega/Zeta/ConclusionLocalizedSingleAxisAnomalyVanishing.lean:31:`ℤ[S⁻¹]` admit a common supported denominator, so they lie in the same rank-`1` subgroup
lean/InfoGeometry/Algebra/ZornBdGDerivationBridge.lean:18:All lemmas and theorems are proven natively in Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Algebra/Zorn/ConcreteComposition.lean:15:No wrappers. No `sorry`.
lean/Omega/Zeta/FiniteDefectCompleteReconstruction.lean:148:`2κ - 1` admit a concrete nonuniqueness witness. -/
lean/Omega/Folding/BlockFoldsatNpComplete.lean:48:/-- SAT instances that admit a concrete satisfying assignment. -/
lean/InfoGeometry/Topology/FredholmRegularizedDeterminantBridge.lean:33:All proofs are 100% native in Lean 4 with 0 `sorry` and 0 custom axioms.
lean/InfoGeometry/Algebra/GoldenMeanShift.lean:22:NO `sorry`, NO `ax!om`, NO `sorry`. Every line is kernel-checked.
lean/InfoGeometry/Topology/CompletedZetaPotentialAndRealGibbsFisherBridge.lean:29:All proofs are 100% native in Lean 4 with 0 `sorry`, 0 custom axioms, and no conjectural overreach.
lean/InfoGeometry/Algebra/Zorn/G2TwoConcreteWeylGroup.lean:22:All proofs are native Mathlib with 0 `sorry`s.
lean/InfoGeometry/Algebra/Zorn/G2BruhatCellDecomposition.lean:15:All proofs are native Mathlib with 0 `sorry`s and 0 custom axioms.
lean/Omega/Zeta/XiHorizonZkFiberpathStokesDiscriminant.lean:47:/-- Concrete fiber-path package: square-closed transcripts admit a potential reconstruction, and
lean/InfoGeometry/Topology/RiemannHypothesisHilbertPolyaBridge.lean:29:All theorems are 100% native Lean 4 with 0 `sorry` and 0 custom axioms.
lean/Omega/Zeta/AppOffcriticalRadiusCompression.lean:40:disk, and both `|w_ρ|²` and `1 - |w_ρ|²` admit the stated closed forms.
lean/Omega/Zeta/XiGoldenW1TrueTwoPhaseLimit.lean:9:Fibonacci subsequential constants on the even/odd phases, and therefore cannot admit a single
lean/InfoGeometry/Algebra/NoFaithfulAssociativeModel.lean:17:No wrappers. No structures. No `sorry`.
lean/InfoGeometry/Topology/MontgomeryPairCorrelationBridge.lean:30:All proofs are 100% native in Lean 4 with 0 `sorry` and 0 custom axioms.
lean/InfoGeometry/Algebra/Zorn/G2CyclotomicPoincareFactorization.lean:18:All proofs are native Mathlib polynomial identities with zero `sorry`s.
lean/InfoGeometry/Algebra/Zorn/G2SteinbergPositiveRoots.lean:17:with 0 `sorry`s.
lean/InfoGeometry/Algebra/BaezG2DerivationExponentialBridge.lean:34:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Algebra/SplitAlbertF4Classification.lean:24:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Algebra/Zorn/G2BNBruhatFramework.lean:29:All proofs are native Mathlib with 0 `sorry`s and 0 custom axioms.
lean/InfoGeometry/Topology/ZeroMultiplicityResidueBridge.lean:30:All theorems are 100% genuine Lean 4 proofs with 0 `sorry` and 0 custom axioms.
lean/InfoGeometry/Algebra/HypercomplexTriadMatrix.lean:18:No `sorry`.
lean/InfoGeometry/Algebra/Zorn/ConcreteBarrier.lean:18:No `sorry`.
lean/InfoGeometry/Algebra/Zorn/G2ChevalleyPoincareCombinatorics.lean:21:All theorems here are kernel-checked algebraic/combinatorial identities with 0 `sorry`s.
lean/InfoGeometry/Algebra/Zorn/Concrete.lean:9:No wrappers. No abstract datum. No `sorry`.
lean/Omega/GroupUnification/FoldbinEquitableLumpabilitySpectralRigidity.lean:8:eigenvalues are the ones that admit a lift through the intertwining matrix, and the random-walk
lean/InfoGeometry/Topology/CompletedZetaV4CharacterDecompositionBridge.lean:34:All proofs are 100% native in Lean 4 with 0 `sorry`, 0 custom axioms, and no conjectural overreach.
lean/InfoGeometry/Topology/RiemannZetaMathlibVicinityBridge.lean:33:All proofs are native, verified, with 0 `sorry` and 0 custom axioms.
lean/Omega/CircleDimension/FiniteLocalizationSolenoidQuotientEmbeddingRigidity.lean:25:/-- Finite-localization solenoids always admit the torus quotient coming from the compact exact
lean/InfoGeometry/Canonical/AmplituhedronDifferentialResidue.lean:26:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/Omega/POM/ProjectionBudget.lean:18:because values and congruence classes admit multiple representatives before choosing a section. -/
lean/InfoGeometry/Canonical/BisognanoWichmannSouriauUnification.lean:34:All proofs are 100% native Lean 4 Mathlib proofs with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Canonical/LeeYangAsanoMobiusNative.lean:25:No `sorry`.
lean/InfoGeometry/External/Auto/RegularizationCayleyPipeline.lean:10:work behind a `sorry`.  The finite SymPy property in
lean/InfoGeometry/Canonical/AsanoRuellePoleExclusion.lean:9:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/SouriauCoadjointOrbitBridge.lean:24:All proofs are complete in native Mathlib 4 with zero `sorry`s and zero custom axioms.
lean/Omega/POM/DeltaqMeanSquareRhCriterion.lean:24:/-- Supercritical regime: the weighted partial sums admit explicit exponential lower and upper
lean/Omega/Conclusion/ComovingDefectFixedRadialWindowNonhiding.lean:43:exact `L¹` and `L∞` formulas both admit explicit positive lower bounds controlled only by the
lean/InfoGeometry/Meta/OwnerTarget.lean:43:  A `sorry` in an owner-target proof is machine-visible closure debt.
lean/InfoGeometry/Meta/ThermodynamicGEORegulation.lean:37:  fitness : ℝ          -- between 0 and 1 (1 = compiles, 0 = sorry)
lean/InfoGeometry/Meta/HonestyPolicy.lean:14:- if it does not exist yet, expose the gap explicitly as `sorry` or an
lean/InfoGeometry/Meta/HonestyPolicy.lean:41:  /-- Explicit `sorry` is acceptable only as visible debt. -/
lean/InfoGeometry/Meta/HonestyPolicy.lean:45:  /-- Banner text must not claim property readback when `sorry` remains. -/
lean/InfoGeometry/Meta/HonestyPolicy.lean:65:      "If a Mathlib-rooted derivation chain is missing, expose the gap explicitly as sorry or an explicit zero-datum. Do not hide debt behind fake witnesses, empty shells, or misleading certification banners." }
lean/InfoGeometry/Meta/ClosureAttribute.lean:11:anchored to the DAG, and free of `sorry` or `sorry`.
lean/Omega/POM/DerivedFoldGoldenRationalPowerUnitObstruction.lean:29:/-- Lucas numbers admit the expected `φ^n + ψ^n` closed form. -/
lean/InfoGeometry/Meta/Admission.lean:141:      mkAdmissionReason syntheticDecl "trust.sorry" "error"
lean/InfoGeometry/Meta/StrictDef.lean:18:  , ``Lean.Parser.Term.«sorry»
lean/InfoGeometry/Meta/StrictDef.lean:31:      "strict {declKind} `{declName}` uses forbidden term syntax (`by`, `sorry`, or `unsafe`) in its type."
lean/InfoGeometry/Meta/StrictDef.lean:34:      "strict {declKind} `{declName}` uses forbidden term syntax (`by`, `sorry`, or `unsafe`) in its value."
lean/InfoGeometry/Meta/StrictDef.lean:291:It accepts only ordinary `def` syntax and rejects tactic blocks, `sorry`, and
lean/Omega/Conclusion/FiniteVerificationClosureComplexityTrilemma.lean:20:undecidable equivalence relation cannot admit a finite-valued computable complete invariant.
lean/InfoGeometry/Canonical/ContinuousDeRhamPotentialBridge.lean:28:All proofs are complete in native Mathlib 4 with zero `sorry`s and zero custom axioms.
lean/Omega/POM/NormalformVsTuringBudgetUndecidable.lean:34:/-- Finite rewrite slices admit a minimal audit representative, but unrestricted semantic classes
lean/Omega/POM/NormalformVsTuringBudgetUndecidable.lean:35:do not admit a global implementation-independent canonical representative. -/
lean/InfoGeometry/Canonical/OperatorModularBridge.lean:15:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/Omega/POM/KinkPrincipleQSelection.lean:31:admit an optimal point on the finite kink set. -/
lean/Omega/Conclusion/LeyangRho45AffineCoordinateSystemOnS5Simplex.lean:7:`ρ₅/ρ₄` coordinates admit the explicit inverse formulas already recorded in the audited
lean/Omega/Frontier/Conjectures.lean:9:/-- The defect process should admit a uniform spectral gap. -/
lean/InfoGeometry/Canonical/LieOrbitInfinitesimal.lean:13:No wrappers. No `sorry`.
lean/Omega/Conclusion/ModpSingularityForcesGreenBadPrime.lean:17:cannot admit an integral inverse scalar. -/
lean/Omega/Conclusion/FixedscalePowerSumSharpThresholdMaxfiber.lean:50:two moments still admit a distinct competitor. Thus the sharp threshold agrees with the max fiber
lean/Omega/Conclusion/ScreenArithmeticShadowAdditiveLinearizationObstruction.lean:5:/-- Idempotent meet semilattices admit no nontrivial additive shadow in `(ℕ^k, +)`.
lean/InfoGeometry/Canonical/ModularTensorInduction.lean:15:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/SO55MatrixCliffordBivectorRealization.lean:43:/-- 🏆 MASTER UNIFIED CAPSTONE SYNTHESIS: Native verification package with 0 sorry and 0 datum. -/
lean/Omega/Conclusion/ScreenExactizationIndependentKernel.lean:43:/-- The partial screen `S0` and its independent kernel `I0` admit the same feasible completions. -/
lean/InfoGeometry/Canonical/BayesianConformalCompression.lean:16:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/RHNeighbourhoodCrystallographicCapstone.lean:20:is sorry-free and builds on native Mathlib 4:
lean/InfoGeometry/Canonical/RHNeighbourhoodCrystallographicCapstone.lean:49:No `OPEN` edges, no `sorry`, no analytical claims.
lean/InfoGeometry/Canonical/RHNeighbourhoodCrystallographicCapstone.lean:169:Every edge is a proved theorem. No sorry, no scaffolding.
lean/Omega/Conclusion/SublinearExcitationFilterInsufficient.lean:10:/-- Concrete data for the conclusion-level contradiction: the excitation counts `k b` admit an
lean/InfoGeometry/Canonical/LieOrbitSymmetryChart2x2.lean:9:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/CognitiveShadow.lean:89:      triggerTerms := #["sorry", "proof debt", "hole"]
lean/InfoGeometry/Canonical/KreinCuntzKriegerPZeroBridge.lean:13:a positive-definite Hilbert metric on the P₀ physical sector without any `sorry`.
lean/Omega/Conclusion/EssentialPrimeAxisMinimality.lean:26:/-- Paper label: `thm:conclusion-essential-prime-axis-minimality`. Good primes admit a finite
lean/Omega/Conclusion/EssentialPrimeAxisMinimality.lean:27:singleton stable label on the unramified fiber, bad primes admit none, and therefore a prime can
lean/InfoGeometry/Canonical/DeRhamThermodynamicPotential.lean:27:All proofs are complete in native Mathlib with zero `sorry`s.
lean/InfoGeometry/Canonical/RindlerWeylDecomposition.lean:21:No placeholders. No `sorry`.
lean/Omega/Conclusion/GoldenLucasLinearCyclotomicGate.lean:12:admit no midpoint index. -/
lean/InfoGeometry/Canonical/MajoranaKitaevSpinorBridge.lean:18:It does not depend on the sorry-equivalent modular spinor layer.
lean/InfoGeometry/Canonical/KnillLaflammeQEC.lean:10:Full native proofs with zero `sorry`s.
lean/InfoGeometry/Canonical/SplitCliffordVacuumExpectation.lean:15:No placeholders. No `sorry`.
lean/InfoGeometry/Canonical/ErlangenLanglandsQuantumBundle.lean:28:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Canonical/DualExponentialArchitectureMaster.lean:42:All proofs are complete in native Mathlib 4 with ZERO `sorry`s and ZERO custom axioms.
lean/InfoGeometry/Canonical/LeeYangAsanoNativeCore.lean:17:No `sorry`.
lean/InfoGeometry/Canonical/ThermodynamicsFirstLaw.lean:29:All proofs are complete in native Mathlib with zero `sorry`s.
lean/InfoGeometry/Canonical/TomitaBregmanDuality.lean:21:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/SplitCliffordChiralProjection.lean:17:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/QuantumDeformationRootBridge.lean:15:No infinite-dimensional representation theory, no analytic continuation, no sorry.
lean/InfoGeometry/Canonical/AsanoRuelleTopologicalEndpoint.lean:20:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/CartanSuperbracketClosure.lean:29:No `sorry`.
lean/InfoGeometry/Canonical/CantorHaarDiracSea.lean:18:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/ModularSL2R.lean:11:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/AsanoRuelleCounterexample.lean:15:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/ZetaSouriauMetriplecticFlowMasterBridge.lean:49:statements use native Mathlib 4 and do not introduce `sorry` or custom axioms.
lean/InfoGeometry/Canonical/ZornDerivationExponentialAutomorphism.lean:24:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Canonical/RedlineGrandSynthesis.lean:27:All proofs are complete in native Mathlib 4 with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Canonical/AlgebraicDerivations.lean:13:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/CrystallographicRootCyclotomicBridge.lean:18:Every theorem is proved natively using Mathlib lemmas. No `sorry`, no
lean/InfoGeometry/Canonical/GrothendieckErlangenProjectiveBridge.lean:21:All proofs are complete in native Mathlib with zero `sorry`s.
lean/InfoGeometry/Canonical/DrazinAnomalousProjector.lean:16:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/SplitCliffordFiniteCurrentObstruction.lean:21:No `sorry`.
lean/InfoGeometry/Canonical/TopologicalGroupIsoExpLog.lean:13:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/GrandCanonicalSouriau.lean:18:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/DimensionAgnosticModularKLDivergence.lean:7:remaining fully constructive (no `sorry`).
lean/InfoGeometry/Canonical/SuperKahlerModularSpinors.lean:16:laws.  The former declarations in this file were unsupported `sorry`-based
lean/InfoGeometry/Canonical/SplitCliffordJordanWignerTwoModeCurrent.lean:13:No `sorry`.
lean/InfoGeometry/Canonical/KreinMajoranaZeroModeBlock.lean:11:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/ChiralKKTIsolation.lean:11:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/EmergentSpacetimeArchitecture.lean:38:All proofs are complete in native Mathlib 4 with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Canonical/FenchelExpLogCore.lean:14:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/SplitCliffordTwoModeWick.lean:16:No placeholders. No `sorry`.
lean/InfoGeometry/Canonical/DepthLogScaleInvariant.lean:21:No `sorry`.
lean/InfoGeometry/Canonical/GaugeGroups.lean:14:Dead declarations (`SU2N`, `block_embedding_*`) removed — sorry-equivalent
lean/InfoGeometry/Canonical/GaugeGroups.lean:15:with zero external consumers. See `reports/dag/sorry-equivalence.md`.
lean/InfoGeometry/Canonical/SO3RotationFenchel.lean:14:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/SuperHolographicEffectiveActionBridge.lean:24:All proofs are complete in native Mathlib 4 with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Canonical/HypothesisToTheoremPipeline.lean:29:All proofs are complete in native Mathlib 4 with ZERO `sorry`s and ZERO custom axioms.
lean/InfoGeometry/Canonical/GeneralizedOperatorChiral.lean:9:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/PrimeLeeYangLargeDeviation.lean:24:sole authority; no `sorry`, no analytic limit, and no measure-theoretic LDP
lean/InfoGeometry/Canonical/LieFenchelQuadratic.lean:15:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/SplitCliffordTwoModeTrace.lean:11:No placeholders. No `sorry`.
lean/InfoGeometry/Canonical/MaurerCartanFactorization.lean:24:All proofs are complete in native Mathlib 4 with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Canonical/LieOrbitAdjointInvariants.lean:13:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/LeeYangAsanoDigest.lean:896:`Analysis.AsanoContractionNative` (no `sorry`).
lean/InfoGeometry/Canonical/BraidKMSG2Bridge.lean:18:former declarations in this file used `sorry` for precisely those missing
lean/InfoGeometry/Canonical/ErlangenObservableBundle.lean:32:All proofs are complete in native Mathlib 4 with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Canonical/EmergentSpacetimeQuantumGeometryBridge.lean:30:All theorems are proved in native Mathlib 4 with zero `sorry`s.
lean/InfoGeometry/Canonical/ModularLorentzBoost.lean:9:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/GrandMathematicalUnification.lean:33:All theorems are fully proved in native Mathlib 4 with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Canonical/WeylCharacterThetaBridge.lean:16:No `sorry`, no analytic continuation, no infinite series. Every theorem
lean/InfoGeometry/Canonical/SouriauInfinitesimalInvariance.lean:8:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/MadelungHydrodynamicPressureBridge.lean:58:proved natively without a single `sorry`.
lean/InfoGeometry/Canonical/CanonicalDerivationSpinBivector55.lean:89:/-- 🏆 MASTER SYNTHESIS: Fully verified native theorem package with 0 sorry and 0 external datum. -/
lean/InfoGeometry/Canonical/EmergentSouriauQGTBridge.lean:31:All proofs are complete in native Mathlib 4 with zero `sorry`s.
lean/InfoGeometry/Canonical/CliffordWaveletAnalyticBridge.lean:17:No `sorry`.
lean/InfoGeometry/Canonical/LeeYangAsanoScaleBoundedEscapeBridge.lean:56:/-! ## Bounded sets admit a positive scale escape witness -/
lean/InfoGeometry/Canonical/PeirceProjectorGrothendieckClass.lean:18:All proofs are natively verified in Lean 4 with zero `sorry`s.
lean/InfoGeometry/Canonical/QuaternionCoaxialOrbit.lean:10:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/UHFModularColimit.lean:28:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
```

- Total placeholder occurrences in tracked Lean tree: 298

## Axiom declarations

```text
```
- Total explicit axiom declarations: 0

## Namespace audit

```text
[audit] Project namespace: InfoGeometry
[audit] Scanning root:       ./lean/InfoGeometry

