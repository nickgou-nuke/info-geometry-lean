# Theory Audit Report

Generated: 2026-08-22 10:45:33Z

## Build toolchain status
- lake: available (/home/goutev/.elan/bin/lake)
```bash
Lake version 5.0.0-src+978f81d (Lean version 4.28.1)
```

## Placeholder proof debt (sorry/admit)

```text
lean/sandbox/GoldenMeanShift.lean:22:NO `sorry`, NO `axiom`, NO `admit`. Every line is kernel-checked.
lean/InfoGeometry/Combinatorics/BinaryPCGolayBridge.lean:37:All proofs are complete native Mathlib 4 with zero `sorry`s, zero placeholders, and zero custom axioms.
lean/InfoGeometry/SelfReference/Shadow.lean:64:| ShadowKind.sorryDebt => "explicit sorry in proof body"
lean/InfoGeometry/NCG/DualExponentialTrifoldBridge.lean:34:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/NCG/NoncommutativeCyclicCocycle.lean:20:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/NCG/CategoricalInductiveColimitKMSBridge.lean:25:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/NCG/NoncommutativeDifferentialCalculus.lean:18:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Automorphic/HeckePurification.lean:82:  `Prop`/`sorry` placeholder with a concrete theorem-shaped obligation.
lean/InfoGeometry/NCG/NoncommutativeNoetherPoisson.lean:20:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/NCG/NoncommutativeOperatorMonotoneMetric.lean:22:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/NCG/CategoricalColimitStateDescent.lean:23:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Continuous/DeRhamUnifiedCorridor.lean:36:All theorems are 100% kernel-checked in native Mathlib 4 with zero `sorry`s.
lean/InfoGeometry/Continuous/PositiveOrthant.lean:30:All proofs are complete in native Mathlib 4 with zero `sorry`s.
lean/InfoGeometry/Continuous/Exactness.lean:26:All proofs are complete in native Mathlib 4 with zero `sorry`s.
lean/InfoGeometry/Application/OperatorFreudenthalBoundary.lean:167:  /-- Boundary states sorry Drazin surgery. -/
lean/InfoGeometry/QuantumGeometry/KreinToHilbertCartanBridge.lean:28:All proofs are native Mathlib 4 derivations checked by the kernel with zero `sorry`s.
lean/InfoGeometry/QuantumGeometry/KahlerSouriauInformationBridge.lean:22:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/QuantumGeometry/Unification.lean:15:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/QuantumGeometry/TangentCotangentSymplecticBridge.lean:15:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/QuantumGeometry/BerryKeatingDilationBridge.lean:34:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/QuantumGeometry/TensorBridge.lean:20:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/Agent/CompilerBridgeCore.lean:705:    s!"Declaration '{declName}' contains `sorry`."
lean/InfoGeometry/Probability/ExpLogRNDerivation.lean:45:All proofs are 100% native Mathlib with zero `sorry`s, zero placeholders, and zero custom axioms.
lean/InfoGeometry/Probability/HomologicalProbability.lean:838:Type III von Neumann factors sorry no finite normal tracial state.
lean/InfoGeometry/InformationGeometry/ItakuraSaitoBregmanBridge.lean:16:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/InformationGeometry/BKMBipartiteTensor.lean:26:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/InformationGeometry/BKMMetricModularBridge.lean:21:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/InformationGeometry/KMSThermodynamicIdentity.lean:20:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/InformationGeometry/ArakiDonaldVariational.lean:24:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/InformationGeometry/BurgSteinSelfConcordance.lean:17:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Lie/SplitOctonionDerivationSpinRep.lean:16:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Lie/G2TwoRealSplitClassification.lean:38:no `sorry`, no external enumeration is invoked inside this file itself.
lean/InfoGeometry/Topology/SymbolicLatentObservedPathImageCompHausEvaluation.lean:10:inclusion maps sorry a genuine `CompHaus` source/target packaging.  The
lean/InfoGeometry/Lie/SouriauBregmanDualityBridge.lean:17:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Lie/SO55MatrixLieSubalgebra.lean:23:are mechanically verified in Lean 4 with ZERO `sorry`s and ZERO custom axioms.
lean/InfoGeometry/LogarithmicBridge.lean:35:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Lie/CartanKreinNeutralSignatureBridge.lean:25:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Lie/CartanCosetRiemannCurvatureBridge.lean:26:All proofs are native Lean 4 with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Lie/G2CartanSymmetricSpaceIdentification.lean:23:and previously verified lemmas. No `sorry`, no wrappers.
lean/InfoGeometry/Topology/CompletedZetaV4CharacterBridge.lean:28:All proofs are 100% genuine Lean 4 proofs with 0 `sorry` and 0 custom axioms.
lean/InfoGeometry/Lie/SplitG2SL3ModuleDecomposition.lean:23:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Topology/MobiusDeRhamMonodromy.lean:29:## Verified theorems (no sorry)
lean/InfoGeometry/Topology/SymbolicLatentVaryingCarrierQuotientCompHausLimit.lean:8:and observation-range diagrams sorry genuine `CompHaus` limits.  This owner
lean/InfoGeometry/Clifford/FanoOctonionParavector.lean:12:All proofs are native and closed without sorry.
lean/InfoGeometry/Analysis/LaplaceUniqueness.lean:302:If two Laplace data agree on the same Bromwich contour and both sorry the
lean/InfoGeometry/Modular/SemidirectExteriorAlgebra.lean:15:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/CommutantSemidirectProduct.lean:16:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/DualExponentialCommutatorBridge.lean:15:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/EntropyMonotonicity.lean:17:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/QuantumDataProcessingInequality.lean:27:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/SelfConcordantBarrierTriple.lean:25:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Clifford/ConformalReflection55.lean:36:These are **native Lean proofs** — no axioms, sorry, or external certificates.
lean/InfoGeometry/Modular/SemidirectAutomorphismGroup.lean:26:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/ConcreteOperatorModularBridge.lean:17:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/QuantumRelativeEntropyMonotonicity.lean:20:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/Noncommutative.lean:24:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/ModularCocycleKMSBridge.lean:49:All proofs are complete in native Mathlib 4 with zero `sorry`s, zero wrappers, and zero custom axioms.
lean/InfoGeometry/Modular/ModularTimeSemigroupBridge.lean:19:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/DualExponentialBerezinianAutomorphismBridge.lean:21:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/TrifoldRadonNikodymBridge.lean:17:All proofs are complete in native Mathlib with zero `sorry`s.
lean/InfoGeometry/Modular/SchrodingerGKSL.lean:20:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/GKSLDissipatorAlgebraic.lean:18:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/WeylPfaffianDeterminantTriple.lean:19:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/TrifoldClassification.lean:12:characterization with zero `sorry`s in native Mathlib.
lean/InfoGeometry/Modular/OperatorKMSThermodynamicIdentity.lean:25:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/KMSColimitExtension.lean:24:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/InnerDerivationLieIdeal.lean:18:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Modular/ZetaRegularizedDeterminantBridge.lean:20:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/Omega/POM/OracleCapacityKolmogorovSpectrum.lean:12:points in the fiber over `x` admit a description of length at most `B`, while `fiberContainment`
lean/Omega/POM/FractranPermutationEmbeddingLength.lean:52:/-- Finite permutations admit a prime-encoded FRACTRAN realization, and any program carrying a
lean/InfoGeometry/Analysis/LogDetSelfConcordantBarrier.lean:21:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Analysis/AsanoRuelleBasicBranches.lean:16:No `sorry`.
lean/InfoGeometry/Physics/OperatorCoefficientZornBdGBridge.lean:43:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Tooling/VacuityCritic.lean:24:    field.value != "sorry" && field.value != "sorry"
lean/InfoGeometry/LLM/AttentionEntropyProductionFlow.lean:27:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Physics/SplitG2SL3ModuleDecomposition.lean:27:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Physics/ZornBdGSuperconductingExponentialBridge.lean:30:All theorems are proved natively in Lean 4 with Mathlib, with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Physics/ZornBdGDerivationBridge.lean:12:All lemmas and theorems are proven natively in Mathlib with zero `sorry`s.
lean/InfoGeometry/External/Auto/BlackHoleHolography.lean:10:the scalar entropy algebra below is proved without axioms or `sorry`.
lean/InfoGeometry/Architecture/CartanCosetManifold.lean:19:All proofs are complete in native Lean 4 with zero `sorry`s and zero custom axioms.
lean/DAG/DisconnectedAudit.lean:25:--   3. sorry_incomplete   : proof uses sorry (debt, not fake root)
lean/DAG/DisconnectedAudit.lean:95:/-- Check if a declaration's proof uses sorry. -/
lean/DAG/DisconnectedAudit.lean:104:      all.any (fun r => r.toString == "sorryAx" || r.toString == "sorry")
lean/DAG/DisconnectedAudit.lean:107:/-- Collect axiom/sorry names from a declaration. -/
lean/DAG/DisconnectedAudit.lean:119:          axioms := axioms.push s!"sorry:{n.toString}"
lean/DAG/DisconnectedAudit.lean:415:    lines := lines.push "These capstones use `sorry` in their proofs. The statements might be true"
lean/InfoGeometry/Architecture/MatrixSymmetricConeFisherRao.lean:19:   proven natively with zero `sorry`s using the cyclic property of the matrix trace.
lean/InfoGeometry/Architecture/MatrixSymmetricConeFisherRao.lean:24:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Architecture/CartanGeodesicSymmetry.lean:27:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/DAG/EckmannHodge.lean:12:All `sorry` debt is closed. Every theorem is a genuine algebraic proof.
lean/InfoGeometry/Topology/CliffordMobiusDeRhamMonodromy.lean:23:## Verified theorems (no sorry)
lean/InfoGeometry/Meta/OwnerTarget.lean:43:  A `sorry` in an owner-target proof is machine-visible closure debt.
lean/DAG/InfoTreeExtract.lean:216:          isSorrySourceScan := refs.contains "sorryAx" || refs.contains "sorry"
lean/InfoGeometry/Meta/ThermodynamicGEORegulation.lean:37:  fitness : ℝ          -- between 0 and 1 (1 = compiles, 0 = sorry)
lean/InfoGeometry/Topology/WeierstrassHadamardDivisorBridge.lean:30:All proofs are 100% native in Lean 4 with 0 `sorry` and 0 custom axioms.
lean/InfoGeometry/Meta/HonestyPolicy.lean:14:- if it does not exist yet, expose the gap explicitly as `sorry` or an
lean/InfoGeometry/Meta/HonestyPolicy.lean:41:  /-- Explicit `sorry` is acceptable only as visible debt. -/
lean/InfoGeometry/Meta/HonestyPolicy.lean:45:  /-- Banner text must not claim property readback when `sorry` remains. -/
lean/InfoGeometry/Meta/HonestyPolicy.lean:65:      "If a Mathlib-rooted derivation chain is missing, expose the gap explicitly as sorry or an explicit zero-datum. Do not hide debt behind fake witnesses, empty shells, or misleading certification banners." }
lean/InfoGeometry/Meta/ClosureAttribute.lean:11:anchored to the DAG, and free of `sorry` or `sorry`.
lean/InfoGeometry/Topology/XiHardyZNormalizationBridge.lean:28:All proofs are 100% genuine Lean 4 proofs with 0 `sorry` and 0 custom axioms.
lean/InfoGeometry/Meta/Admission.lean:141:      mkAdmissionReason syntheticDecl "trust.sorry" "error"
lean/DAG/FunctionalGaussJordan.lean:17:All proofs are standard linear algebra — no axioms, no sorry debt.
lean/InfoGeometry/Meta/StrictDef.lean:18:  , ``Lean.Parser.Term.«sorry»
lean/InfoGeometry/Meta/StrictDef.lean:31:      "strict {declKind} `{declName}` uses forbidden term syntax (`by`, `sorry`, or `unsafe`) in its type."
lean/InfoGeometry/Meta/StrictDef.lean:34:      "strict {declKind} `{declName}` uses forbidden term syntax (`by`, `sorry`, or `unsafe`) in its value."
lean/InfoGeometry/Meta/StrictDef.lean:291:It accepts only ordinary `def` syntax and rejects tactic blocks, `sorry`, and
lean/InfoGeometry/External/Auto/RegularizationCayleyPipeline.lean:10:work behind a `sorry`.  The finite SymPy property in
lean/Omega/SPG/ErrorThreshold.lean:157:    exponent ratios `r` and `p^2 r` admit overlapping admissible observation intervals, and
lean/InfoGeometry/Topology/NativeMathlibZetaMetriplecticFlowBridge.lean:16:- ZERO `sorry`
lean/InfoGeometry/Synthesis/OnsagerOperatorDifferentialCalculus.lean:18:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Information/SouriauLieGroupThermodynamics.lean:35:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Information/ModularCocycleKMSBridge.lean:37:All proofs are 100% native Mathlib with zero `sorry`s, zero placeholders, and zero custom axioms.
lean/InfoGeometry/Information/MasterArchetypeConvexDuality.lean:42:All theorems are fully proved with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Information/ModularSurprisalDerivationBridge.lean:21:All proofs are complete with 0 `sorry`s, 0 custom axioms, and 0 placeholders.
lean/InfoGeometry/Information/UniversalDualityQuadrangle.lean:29:All theorems are fully proved in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Topology/FredholmRegularizedDeterminantBridge.lean:33:All proofs are 100% native in Lean 4 with 0 `sorry` and 0 custom axioms.
lean/InfoGeometry/Topology/CompletedZetaPotentialAndRealGibbsFisherBridge.lean:29:All proofs are 100% native in Lean 4 with 0 `sorry`, 0 custom axioms, and no conjectural overreach.
lean/Omega/POM/DeltaqMeanSquareRhCriterion.lean:24:/-- Supercritical regime: the weighted partial sums admit explicit exponential lower and upper
lean/InfoGeometry/Topology/RiemannHypothesisHilbertPolyaBridge.lean:29:All theorems are 100% native Lean 4 with 0 `sorry` and 0 custom axioms.
lean/Omega/POM/DerivedFoldGoldenRationalPowerUnitObstruction.lean:29:/-- Lucas numbers admit the expected `φ^n + ψ^n` closed form. -/
lean/Omega/POM/KinkPrincipleQSelection.lean:31:admit an optimal point on the finite kink set. -/
lean/InfoGeometry/Topology/MontgomeryPairCorrelationBridge.lean:30:All proofs are 100% native in Lean 4 with 0 `sorry` and 0 custom axioms.
lean/InfoGeometry/Topology/ZeroMultiplicityResidueBridge.lean:30:All theorems are 100% genuine Lean 4 proofs with 0 `sorry` and 0 custom axioms.
lean/Omega/POM/NormalformVsTuringBudgetUndecidable.lean:34:/-- Finite rewrite slices admit a minimal audit representative, but unrestricted semantic classes
lean/Omega/POM/NormalformVsTuringBudgetUndecidable.lean:35:do not admit a global implementation-independent canonical representative. -/
lean/InfoGeometry/Canonical/LeeYangAsanoMobiusNative.lean:25:No `sorry`.
lean/InfoGeometry/Canonical/AsanoRuellePoleExclusion.lean:9:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/SouriauCoadjointOrbitBridge.lean:24:All proofs are complete in native Mathlib 4 with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Physics/SplitOctonionDerivationSpinRep.lean:24:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Canonical/AmplituhedronDifferentialResidue.lean:26:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Canonical/ContinuousDeRhamPotentialBridge.lean:28:All proofs are complete in native Mathlib 4 with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Canonical/OperatorModularBridge.lean:15:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Canonical/BisognanoWichmannSouriauUnification.lean:34:All proofs are 100% native Lean 4 Mathlib proofs with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/AsanoRuelle/MobiusInversion.lean:9:No placeholders. No `sorry`.
lean/InfoGeometry/AsanoRuelle/AsanoRuelleCounterexample.lean:12:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/LieOrbitInfinitesimal.lean:13:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/BayesianConformalCompression.lean:16:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/KreinCuntzKriegerPZeroBridge.lean:13:a positive-definite Hilbert metric on the P₀ physical sector without any `sorry`.
lean/InfoGeometry/Topology/CompletedZetaV4CharacterDecompositionBridge.lean:34:All proofs are 100% native in Lean 4 with 0 `sorry`, 0 custom axioms, and no conjectural overreach.
lean/InfoGeometry/Algebra/NilpotentNonunit.lean:11:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/RindlerWeylDecomposition.lean:21:No placeholders. No `sorry`.
lean/InfoGeometry/Algebra/Zorn/ConcreteComposition.lean:15:No wrappers. No `sorry`.
lean/InfoGeometry/Topology/RiemannZetaMathlibVicinityBridge.lean:33:All proofs are native, verified, with 0 `sorry` and 0 custom axioms.
lean/InfoGeometry/Algebra/Zorn/G2TwoConcreteWeylGroup.lean:22:All proofs are native Mathlib with 0 `sorry`s.
lean/InfoGeometry/Algebra/Zorn/G2BruhatCellDecomposition.lean:15:All proofs are native Mathlib with 0 `sorry`s and 0 custom axioms.
lean/InfoGeometry/Algebra/ZeckendorfBijection.lean:15:NO `sorry`, NO `ax!om`, NO `sorry`. Every line is kernel-checked.
lean/Omega/POM/ProjectionBudget.lean:18:because values and congruence classes admit multiple representatives before choosing a section. -/
lean/InfoGeometry/Canonical/KreinMajoranaZeroModeBlock.lean:11:No wrappers. No `sorry`.
lean/InfoGeometry/OperatorAlgebra/WittenMöbiusBraidBridge.lean:18:All proofs are native Lean 4 derivations checked by the kernel with zero remaining sorry debt.
lean/InfoGeometry/Canonical/PrimeLeeYangLargeDeviation.lean:24:sole authority; no `sorry`, no analytic limit, and no measure-theoretic LDP
lean/InfoGeometry/Canonical/SplitCliffordTwoModeTrace.lean:11:No placeholders. No `sorry`.
lean/InfoGeometry/OperatorAlgebra/SplitOctonionPseudoReal.lean:18:No `sorry`/`ax!om`/`sorry`/property scaffolding is used.
lean/InfoGeometry/Canonical/LeeYangAsanoDigest.lean:896:`Analysis.AsanoContractionNative` (no `sorry`).
lean/InfoGeometry/OperatorAlgebra/ChiralCliffordSplit.lean:17:All proofs are native, formal Lean 4 derivations checked by the kernel with zero sorry debt.
lean/InfoGeometry/OperatorAlgebra/TripotentMatrix2x2.lean:15:All proofs are native Lean 4 derivations checked by the kernel with zero remaining sorry debt.
lean/InfoGeometry/Canonical/ModularTensorInduction.lean:15:No wrappers. No `sorry`.
lean/InfoGeometry/Arithmetic/PolyaHilbertDiracHodgeCantorBridge.lean:19:Plus the internal proof: `SouriauDiracHodgeCoupling` (659 lines, 32 thm, 0 sorry).
lean/InfoGeometry/Arithmetic/LagariasMontagueParityLadderBridge.lean:16:All proofs are native Mathlib with 0 `sorry`s and 0 custom axioms.
lean/InfoGeometry/Canonical/SO55MatrixCliffordBivectorRealization.lean:43:/-- 🏆 MASTER UNIFIED CAPSTONE SYNTHESIS: Native verification package with 0 sorry and 0 datum. -/
lean/InfoGeometry/Algebra/AssociativityObstruction.lean:31:* therefore a genuinely nonassociative algebra cannot sorry such a
lean/InfoGeometry/Canonical/RHNeighbourhoodCrystallographicCapstone.lean:20:is sorry-free and builds on native Mathlib 4:
lean/InfoGeometry/Canonical/RHNeighbourhoodCrystallographicCapstone.lean:49:No `OPEN` edges, no `sorry`, no analytical claims.
lean/InfoGeometry/Canonical/RHNeighbourhoodCrystallographicCapstone.lean:169:Every edge is a proved theorem. No sorry, no scaffolding.
lean/InfoGeometry/Algebra/GogberashviliNilpotentCARBridge.lean:20:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Canonical/LieOrbitSymmetryChart2x2.lean:9:No wrappers. No `sorry`.
lean/InfoGeometry/Algebra/CuntzRecursiveFermionSystem.lean:219:/-! ## Wedge Actions (sorry-free) -/
lean/InfoGeometry/Projective/SplitOctonions/SplitOctonionsLegendre.lean:21:No wrappers. No `sorry`.
lean/InfoGeometry/Projective/SplitOctonions/SplitOctonionsColorStabilizer.lean:14:No wrappers. No `sorry`.
lean/InfoGeometry/Projective/SplitOctonions/ProjectivePolarInvariant.lean:21:No `sorry`.
lean/InfoGeometry/Projective/SplitOctonions/BektasMatrix.lean:14:No wrappers. No `sorry`.
lean/InfoGeometry/Projective/SplitOctonions/ProjectivePolarFiberTransport.lean:22:No `sorry`.
lean/InfoGeometry/Projective/SplitOctonions/ProjectivePolarFiber.lean:19:No `sorry`.
lean/InfoGeometry/Algebra/NonAssocPeirceFrame.lean:26:All proofs are 100% native Mathlib with zero `sorry`s, zero custom axioms, and zero admits.
lean/InfoGeometry/Canonical/CognitiveShadow.lean:89:      triggerTerms := #["sorry", "proof debt", "hole"]
lean/InfoGeometry/Projective/KleinQuadricPlucker.lean:16:No wrappers. No `sorry`.
lean/InfoGeometry/Projective/KleinCrossRatioInvariant.lean:16:No wrappers. No `sorry`.
lean/InfoGeometry/Algebra/ZornBdGDerivationBridge.lean:18:All lemmas and theorems are proven natively in Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Projective/SplitOctonions.lean:16:No `sorry`, no `True` placeholders, no fake Freudenthal determinant.
lean/InfoGeometry/Algebra/GoldenMeanShift.lean:22:NO `sorry`, NO `ax!om`, NO `sorry`. Every line is kernel-checked.
lean/InfoGeometry/Projective/KleinQuadric.lean:23:No `sorry`.
lean/InfoGeometry/Projective/KleinQuadricIncidence.lean:16:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/UHFModularColimit.lean:28:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Projective/Quadrics/AffineSlices.lean:23:No `sorry`.
lean/InfoGeometry/Canonical/DeRhamThermodynamicPotential.lean:27:All proofs are complete in native Mathlib with zero `sorry`s.
lean/InfoGeometry/Canonical/QuaternionCoaxialOrbit.lean:10:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/MajoranaKitaevSpinorBridge.lean:18:It does not depend on the sorry-equivalent modular spinor layer.
lean/InfoGeometry/Lint/NonTriviality.lean:27:* transitive ax!om audit using `Lean.collectAxioms`, with explicit `sorry` treated as honest closure debt when configured;
lean/InfoGeometry/Lint/NonTriviality.lean:57:/-- Permit explicit `sorry` as honest, visible closure debt. -/
lean/InfoGeometry/Lint/Pauli.lean:11:/-- Option to control the Pauli sorry linter. -/
lean/InfoGeometry/Lint/Pauli.lean:100:                  logError m!"[Pauli/Axiom-Surface Seal] {declName} depends on nonstandard `admitAx`; use explicit `sorry` instead of a disguised placeholder."
lean/InfoGeometry/Canonical/KnillLaflammeQEC.lean:10:Full native proofs with zero `sorry`s.
lean/InfoGeometry/Canonical/ErlangenLanglandsQuantumBundle.lean:28:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Canonical/SplitCliffordVacuumExpectation.lean:15:No placeholders. No `sorry`.
lean/InfoGeometry/Canonical/LeeYangAsanoNativeCore.lean:17:No `sorry`.
lean/InfoGeometry/Canonical/DualExponentialArchitectureMaster.lean:42:All proofs are complete in native Mathlib 4 with ZERO `sorry`s and ZERO custom axioms.
lean/InfoGeometry/Canonical/TomitaBregmanDuality.lean:21:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/SplitCliffordChiralProjection.lean:17:No wrappers. No `sorry`.
lean/Omega/SyncKernelWeighted/GmModqRecursionClosure.lean:14:/-- The mod-`q` residue counts admit a finite matrix-coefficient presentation.
lean/InfoGeometry/Arithmetic/ZetaDihedral.lean:15:No deferred interfaces. No certificates. No axioms. No `sorry`.
lean/InfoGeometry/Arithmetic/ChebyshevPrimeEnergyBound.lean:25:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Canonical/ThermodynamicsFirstLaw.lean:29:All proofs are complete in native Mathlib with zero `sorry`s.
lean/InfoGeometry/Arithmetic/SelfConcordantZetaBarrierProofs.lean:6:No deferred interfaces. No certificates. No axioms. No `sorry`.
lean/InfoGeometry/Canonical/AsanoRuelleTopologicalEndpoint.lean:20:No wrappers. No `sorry`.
lean/Omega/EA/Sync10ResetDepthSpectrum.lean:166:other eight target states already admit depth-`5` reset words.
lean/InfoGeometry/Canonical/QuantumDeformationRootBridge.lean:15:No infinite-dimensional representation theory, no analytic continuation, no sorry.
lean/InfoGeometry/Algebra/Zorn/G2CyclotomicPoincareFactorization.lean:18:All proofs are native Mathlib polynomial identities with zero `sorry`s.
lean/InfoGeometry/Algebra/Zorn/G2SteinbergPositiveRoots.lean:17:with 0 `sorry`s.
lean/InfoGeometry/Algebra/Zorn/G2BNBruhatFramework.lean:29:All proofs are native Mathlib with 0 `sorry`s and 0 custom axioms.
lean/InfoGeometry/Algebra/Zorn/ConcreteBarrier.lean:18:No `sorry`.
lean/InfoGeometry/Algebra/Zorn/G2ChevalleyPoincareCombinatorics.lean:21:All theorems here are kernel-checked algebraic/combinatorial identities with 0 `sorry`s.
lean/InfoGeometry/Algebra/Zorn/Concrete.lean:9:No wrappers. No abstract datum. No `sorry`.
lean/InfoGeometry/Algebra/BaezG2DerivationExponentialBridge.lean:34:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Algebra/HypercomplexTriadMatrix.lean:18:No `sorry`.
lean/InfoGeometry/Canonical/ModularSL2R.lean:11:No wrappers. No `sorry`.
lean/InfoGeometry/Algebra/NoFaithfulAssociativeModel.lean:17:No wrappers. No structures. No `sorry`.
lean/InfoGeometry/Algebra/SplitAlbertF4Classification.lean:24:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Canonical/PeirceProjectorGrothendieckClass.lean:18:All proofs are natively verified in Lean 4 with zero `sorry`s.
lean/InfoGeometry/Canonical/CartanSuperbracketClosure.lean:29:No `sorry`.
lean/InfoGeometry/Canonical/ZornDerivationExponentialAutomorphism.lean:24:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Canonical/ZetaSouriauMetriplecticFlowMasterBridge.lean:49:statements use native Mathlib 4 and do not introduce `sorry` or custom axioms.
lean/InfoGeometry/Canonical/RedlineGrandSynthesis.lean:27:All proofs are complete in native Mathlib 4 with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Canonical/CantorHaarDiracSea.lean:18:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/LeeYangAsanoScaleBoundedEscapeBridge.lean:56:/-! ## Bounded sets admit a positive scale escape witness -/
lean/InfoGeometry/Canonical/AlgebraicDerivations.lean:13:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/AsanoRuelleCounterexample.lean:15:No wrappers. No `sorry`.
lean/InfoGeometry/OperatorAlgebra/OperatorExteriorAlgebraGeneral.lean:18:All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Canonical/CliffordWaveletAnalyticBridge.lean:17:No `sorry`.
lean/InfoGeometry/Canonical/GrothendieckErlangenProjectiveBridge.lean:21:All proofs are complete in native Mathlib with zero `sorry`s.
lean/Omega/EA/PrimeRegisterOrbitFiberCoincidence.lean:9:/-- Two prime-register states lie in the same local Fibonacci orbit when they admit a common
lean/InfoGeometry/Canonical/CrystallographicRootCyclotomicBridge.lean:18:Every theorem is proved natively using Mathlib lemmas. No `sorry`, no
lean/InfoGeometry/Canonical/SplitCliffordFiniteCurrentObstruction.lean:21:No `sorry`.
lean/InfoGeometry/Canonical/TopologicalGroupIsoExpLog.lean:13:No wrappers. No `sorry`.
lean/Omega/EA/RewriteCore.lean:119:/-- Any two one-step reducts admit a common normal-form descendant. -/
lean/Omega/EA/RewriteCore.lean:126:/-- Any two reducts admit a common normal-form descendant. -/
lean/InfoGeometry/Canonical/DrazinAnomalousProjector.lean:16:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/GrandCanonicalSouriau.lean:18:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/DimensionAgnosticModularKLDivergence.lean:7:remaining fully constructive (no `sorry`).
lean/InfoGeometry/Canonical/SuperKahlerModularSpinors.lean:16:laws.  The former declarations in this file were unsupported `sorry`-based
lean/InfoGeometry/Canonical/SplitCliffordJordanWignerTwoModeCurrent.lean:13:No `sorry`.
lean/InfoGeometry/Canonical/EmergentSpacetimeArchitecture.lean:38:All proofs are complete in native Mathlib 4 with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Canonical/FenchelExpLogCore.lean:14:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/SplitCliffordTwoModeWick.lean:16:No placeholders. No `sorry`.
lean/InfoGeometry/Canonical/DepthLogScaleInvariant.lean:21:No `sorry`.
lean/Omega/Frontier/Conjectures.lean:9:/-- The defect process should admit a uniform spectral gap. -/
lean/Omega/Zeta/RealInput40GeodesicRamanujanMargin.lean:41:gap exponent is `log (λ_nb² / ρ_nb)`, and both the primitive-orbit and prime-orbit counts admit
lean/Omega/Zeta/XiToeplitzDetVerblunsky.lean:119:/-- Paper label: `thm:xi-toeplitz-det-verblunsky`. The Toeplitz determinants admit the exact
lean/InfoGeometry/Canonical/GaugeGroups.lean:14:Dead declarations (`SU2N`, `block_embedding_*`) removed — sorry-equivalent
lean/InfoGeometry/Canonical/GaugeGroups.lean:15:with zero external consumers. See `reports/dag/sorry-equivalence.md`.
lean/InfoGeometry/OperatorAlgebra/SplitQuaternionSL2Isomorphism.lean:20:All proofs are native Lean 4 derivations checked by the kernel with zero remaining sorry debt.
lean/InfoGeometry/OperatorAlgebra/ChiralRailPlane.lean:19:All relations are verified with native Mathlib proofs and zero `sorry`s.
lean/InfoGeometry/OperatorAlgebra/SplitOctonionLoxodromic.lean:18:All proofs are native Lean 4 derivations checked by the kernel with zero remaining sorry debt.
lean/InfoGeometry/Canonical/SO3RotationFenchel.lean:14:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/SuperHolographicEffectiveActionBridge.lean:24:All proofs are complete in native Mathlib 4 with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Canonical/ChiralKKTIsolation.lean:11:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/HypothesisToTheoremPipeline.lean:29:All proofs are complete in native Mathlib 4 with ZERO `sorry`s and ZERO custom axioms.
lean/InfoGeometry/Canonical/GeneralizedOperatorChiral.lean:9:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/LieFenchelQuadratic.lean:15:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/BraidKMSG2Bridge.lean:18:former declarations in this file used `sorry` for precisely those missing
lean/InfoGeometry/Canonical/MaurerCartanFactorization.lean:24:All proofs are complete in native Mathlib 4 with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Canonical/LieOrbitAdjointInvariants.lean:13:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/MadelungHydrodynamicPressureBridge.lean:58:proved natively without a single `sorry`.
lean/InfoGeometry/Canonical/EmergentSpacetimeQuantumGeometryBridge.lean:30:All theorems are proved in native Mathlib 4 with zero `sorry`s.
lean/InfoGeometry/Canonical/CanonicalDerivationSpinBivector55.lean:89:/-- 🏆 MASTER SYNTHESIS: Fully verified native theorem package with 0 sorry and 0 external datum. -/
lean/InfoGeometry/Canonical/EmergentSouriauQGTBridge.lean:31:All proofs are complete in native Mathlib 4 with zero `sorry`s.
lean/InfoGeometry/Canonical/ErlangenObservableBundle.lean:32:All proofs are complete in native Mathlib 4 with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Canonical/ModularLorentzBoost.lean:9:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/GrandMathematicalUnification.lean:33:All theorems are fully proved in native Mathlib 4 with zero `sorry`s and zero custom axioms.
lean/InfoGeometry/Canonical/SouriauInfinitesimalInvariance.lean:8:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/WeylCharacterThetaBridge.lean:16:No `sorry`, no analytic continuation, no infinite series. Every theorem
lean/Omega/CircleDimension/FiniteLocalizationSolenoidQuotientEmbeddingRigidity.lean:25:/-- Finite-localization solenoids always admit the torus quotient coming from the compact exact
lean/Omega/Zeta/XiOffcriticalDichotomyAcceptableOrNull.lean:14:/-- Off-critical claims either admit the explicit acceptable radial extension with the sharp
lean/Omega/Zeta/XiPrimeRegisterHistoryInverseLimit.lean:118:/-- Finite-history register prefixes admit injective recursive encodings, and the compatible tower
lean/Omega/GroupUnification/FoldbinEquitableLumpabilitySpectralRigidity.lean:8:eigenvalues are the ones that admit a lift through the intertwining matrix, and the random-walk
lean/Omega/Zeta/DerivedZGHardcoreFactorization.lean:59:Euler factors admit the `ζ(σ) / ζ(2σ)` local rewrite, the finite-support sequence stabilizes, and
lean/Omega/Zeta/XiGoldenW1TrueTwoPhaseLimit.lean:9:Fibonacci subsequential constants on the even/odd phases, and therefore cannot admit a single
lean/Omega/UnitCirclePhaseArithmetic/AppHorizonEulerPatch.lean:29:`|w| ≤ r < 1/3` the Euler terms admit a uniform geometric majorant. -/
lean/Omega/Conclusion/ComovingDefectFixedRadialWindowNonhiding.lean:43:exact `L¹` and `L∞` formulas both admit explicit positive lower bounds controlled only by the
lean/Omega/Conclusion/FiniteVerificationClosureComplexityTrilemma.lean:20:undecidable equivalence relation cannot admit a finite-valued computable complete invariant.
lean/Omega/GU/JoukowskyAreaPreservingCayley.lean:22:/-- The normalized semiaxes are reciprocal and admit the usual hyperbolic parametrization. -/
lean/Omega/Conclusion/LeyangRho45AffineCoordinateSystemOnS5Simplex.lean:7:`ρ₅/ρ₄` coordinates admit the explicit inverse formulas already recorded in the audited
lean/Omega/Conclusion/ModpSingularityForcesGreenBadPrime.lean:17:cannot admit an integral inverse scalar. -/
lean/Omega/GU/TerminalWindow6FiniteCompletenessTemplate.lean:27:force unique labeling, and finite audit triples admit a direct equality decision procedure.
lean/Omega/Conclusion/FixedscalePowerSumSharpThresholdMaxfiber.lean:50:two moments still admit a distinct competitor. Thus the sharp threshold agrees with the max fiber
lean/Omega/GU/Window6Affine2FlatRootSliceSelection.lean:38:The three affine-`2`-flat cyclic words admit an explicit lookup against three `B₃` roots in the
lean/Omega/Zeta/ConclusionLocalizedSingleAxisAnomalyVanishing.lean:31:`ℤ[S⁻¹]` admit a common supported denominator, so they lie in the same rank-`1` subgroup
lean/Omega/Conclusion/ScreenExactizationIndependentKernel.lean:43:/-- The partial screen `S0` and its independent kernel `I0` admit the same feasible completions. -/
lean/Omega/Conclusion/ScreenArithmeticShadowAdditiveLinearizationObstruction.lean:5:/-- Idempotent meet semilattices admit no nontrivial additive shadow in `(ℕ^k, +)`.
lean/Omega/Zeta/FiniteDefectCompleteReconstruction.lean:148:`2κ - 1` admit a concrete nonuniqueness witness. -/
lean/Omega/Conclusion/SublinearExcitationFilterInsufficient.lean:10:/-- Concrete data for the conclusion-level contradiction: the excitation counts `k b` admit an
lean/Omega/Zeta/XiHorizonZkFiberpathStokesDiscriminant.lean:47:/-- Concrete fiber-path package: square-closed transcripts admit a potential reconstruction, and
lean/Omega/Conclusion/EssentialPrimeAxisMinimality.lean:26:/-- Paper label: `thm:conclusion-essential-prime-axis-minimality`. Good primes admit a finite
lean/Omega/Conclusion/EssentialPrimeAxisMinimality.lean:27:singleton stable label on the unramified fiber, bad primes admit none, and therefore a prime can
lean/Omega/Zeta/AppOffcriticalRadiusCompression.lean:40:disk, and both `|w_ρ|²` and `1 - |w_ρ|²` admit the stated closed forms.
lean/Omega/Conclusion/GoldenLucasLinearCyclotomicGate.lean:12:admit no midpoint index. -/
lean/Omega/Zeta/XiWindow6MinrepZeckendorfSignatureInjection.lean:47:The `21` minimal reachable representatives admit explicit Zeckendorf signatures; each evaluates to
lean/Omega/Folding/FiberIdentifiableSigmaAlgebraMaximal.lean:8:admit an explicit inverse kernel whose translated pattern counts are read off from the subset
lean/Omega/Folding/BlockFoldsatNpComplete.lean:48:/-- SAT instances that admit a concrete satisfying assignment. -/
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

[audit] Files with namespace InfoGeometry*: 8151
[audit] Files missing namespace InfoGeometry*: 1354

=== Missing namespace InfoGeometry ===
./lean/InfoGeometry/Albert/AlbertCubicDatum.lean
./lean/InfoGeometry/Albert/F4Action.lean
./lean/InfoGeometry/Algebra/AnyonFiniteSpinBraid.lean
./lean/InfoGeometry/Algebra/BerezinianPfaffianBott.lean
./lean/InfoGeometry/Algebra/CARFockBridge_withproofs.lean
./lean/InfoGeometry/Algebra/ChiralGradeReversingMirror.lean
./lean/InfoGeometry/Algebra/ChiralSoldering.lean
./lean/InfoGeometry/Algebra/Cl11Fermions.lean
./lean/InfoGeometry/Algebra/ConfabulationToyModels.lean
./lean/InfoGeometry/Algebra/ConfabulationToyModelsPart2.lean
./lean/InfoGeometry/Algebra/CuntzAlgebra.lean
./lean/InfoGeometry/Algebra/CuntzFibonacciBraidInclusion.lean
./lean/InfoGeometry/Algebra/CuntzToeplitzStarHom.lean
./lean/InfoGeometry/Algebra/Det2.lean
./lean/InfoGeometry/Algebra/FibonacciGradedOffDiagonalBridge.lean
./lean/InfoGeometry/Algebra/FibonacciParafermion.lean
./lean/InfoGeometry/Algebra/Grothendieck.lean
./lean/InfoGeometry/Algebra/H3ZornJordanProduct.lean
./lean/InfoGeometry/Algebra/HodgeDiracDelta.lean
./lean/InfoGeometry/Algebra/HodgeKreinTriFacet.lean
./lean/InfoGeometry/Algebra/Hypothesis1.lean
./lean/InfoGeometry/Algebra/IdeleCuntzSymmetry.lean
./lean/InfoGeometry/Algebra/IdempotentProjector.lean
./lean/InfoGeometry/Algebra/K0FibonacciRing.lean
./lean/InfoGeometry/Algebra/KawamuraCuntzCAR.lean
./lean/InfoGeometry/Algebra/KreinPosNegDecomposition.lean
./lean/InfoGeometry/Algebra/QCCRSupergradingBridge.lean
./lean/InfoGeometry/Algebra/ReducedStructureSpinCertifiedPacket.lean
./lean/InfoGeometry/Algebra/SplitCliffordTransformKernel.lean
./lean/InfoGeometry/Algebra/SuperTraceBerezinian.lean
./lean/InfoGeometry/Algebra/Test.lean
./lean/InfoGeometry/Algebra/TriFacetMatrixRealization.lean
./lean/InfoGeometry/Algebra/TriFacetSpectralPowers.lean
./lean/InfoGeometry/Algebra/TripotentClSUSYBridge.lean
./lean/InfoGeometry/Algebra/TripotentCuntzSUSYBridge.lean
./lean/InfoGeometry/Algebra/TripotentPeirceProjectorBridge.lean
./lean/InfoGeometry/Algebra/UnitizationNonAssoc.lean
./lean/InfoGeometry/Algebra/VerlindeSMatrix.lean
./lean/InfoGeometry/Algebra/ZornBdGDerivationBridge.lean
./lean/InfoGeometry/Algebra/Zorn/_CheckNames.lean
./lean/InfoGeometry/Algebra/Zorn/G2TwoPCAbstractGroup.lean
./lean/InfoGeometry/All.lean
./lean/InfoGeometry/Analysis/All.lean
./lean/InfoGeometry/Analysis/KatzSarnakDensity.lean
./lean/InfoGeometry/Analysis.lean
./lean/InfoGeometry/Analysis/LogarithmicDerivativeBridge.lean
./lean/InfoGeometry/Analytic/HKColimitStructures.lean
./lean/InfoGeometry/Application/BlackHoleEntropyReadout.lean
./lean/InfoGeometry/Application/STUDictionary.lean
./lean/InfoGeometry/Arithmetic/BostConnesFiniteOnsagerBridge.lean
./lean/InfoGeometry/Arithmetic/DirichletModeFactorization.lean
./lean/InfoGeometry/Arithmetic.lean
./lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbert/AnalyticFrontier.lean
./lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbert/Bridge.lean
./lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbert.lean
./lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbert/TraceFormula.lean
./lean/InfoGeometry/Arithmetic/PrimeCantorBooleanCubeBridge.lean
./lean/InfoGeometry/Arithmetic/PrimeCantorLatticeDiracBridge.lean
./lean/InfoGeometry/Arithmetic/PrimeCantorWeylGaugeFockBridge.lean
./lean/InfoGeometry/Arithmetic/PrimeSpinorWittenIndex.lean
./lean/InfoGeometry/Arithmetic/ProjectiveRelativeEntropy.lean
./lean/InfoGeometry/Arithmetic/RHStructural.lean
./lean/InfoGeometry/Arithmetic/SandboxPrimeParafermionRecurrenceTest.lean
./lean/InfoGeometry/Arithmetic/SandboxPrimeThermodynamicStageTest.lean
./lean/InfoGeometry/Arithmetic/ZetaPotentialSign.lean
./lean/InfoGeometry/Arithmetic/ZetaSouriauAttachmentMasterBridge.lean
./lean/InfoGeometry/Arithmetic/ZetaSouriauEntropyMetriplecticBridge.lean
./lean/InfoGeometry/Arithmetic/ZetaSouriauFiniteDifferenceBridge.lean
./lean/InfoGeometry/Arithmetic/ZetaSouriauOnsagerFactorizationBridge.lean
./lean/InfoGeometry/Arithmetic/ZetaSupertraceBridge.lean
./lean/InfoGeometry/Attention/LogSumExpAttention.lean
./lean/InfoGeometry/Audit.lean
./lean/InfoGeometry/auto_blueprints.lean
./lean/InfoGeometry/Automath/Generated/auto_20260721_230011_1.lean
./lean/InfoGeometry/Automath/Generated/auto_20260721_230011_2.lean
./lean/InfoGeometry/Automath/Generated/causal_zorn_presheaf.lean
./lean/InfoGeometry/Automath/Generated/cuntz_fibonacci_resolvent.lean
./lean/InfoGeometry/Automath/Generated/cuntz_shift_commutativity.lean
./lean/InfoGeometry/Automath/Generated/cuntz_yang_baxter.lean
./lean/InfoGeometry/Automath/Generated/entropy_hessian_eq_fisher_inverse.lean
./lean/InfoGeometry/Automath/Generated/hyp_1_spectral_rigidity.lean
./lean/InfoGeometry/Automath/Generated/hyp_2_fibonacci_functional_calculus.lean
./lean/InfoGeometry/Automath/Generated/hyp_3_operator_roots.lean
./lean/InfoGeometry/Automath/Generated/hyp_4_braid_image.lean
./lean/InfoGeometry/Automath/Generated/hyp_5_k_theory.lean
./lean/InfoGeometry/Automath/Generated/hyp_pin55_krein.lean
./lean/InfoGeometry/Automath/Generated.lean
./lean/InfoGeometry/Automath/Generated/omega_auto_omega_bost_connes_kms.lean
./lean/InfoGeometry/Automath/Generated/omega_auto_omega_circle_dimension.lean
./lean/InfoGeometry/Automath/Generated/omega_auto_omega_cuntz_shift.lean
./lean/InfoGeometry/Automath/Generated/omega_auto_omega_golden_ratio_seed.lean
./lean/InfoGeometry/Automath/Generated/omega_auto_omega_walsh_stokes.lean
./lean/InfoGeometry/Automath/Generated/omega_auto_omega_xi_zeta_interface.lean
./lean/InfoGeometry/Automath/Generated/omega_fib_complete.lean
./lean/InfoGeometry/Automath/Generated/omega_fib_gcd.lean
./lean/InfoGeometry/Automath/Generated/omega_fib_succ_pos.lean
./lean/InfoGeometry/Automath/Generated/omega_fib_succ_succ.lean
./lean/InfoGeometry/Automath/Generated/onsager_entropy_production_zero.lean
./lean/InfoGeometry/Automath/Generated/su3_gellmann_lie_algebra.lean
./lean/InfoGeometry/Automath/Generated/test_hyp.lean
./lean/InfoGeometry/Automath.lean
./lean/InfoGeometry/BostConnes/BostConnesThermofield.lean
./lean/InfoGeometry/BottPeriodicityReconciliation.lean
./lean/InfoGeometry/Canonical/AdSCFTEntanglementWedgeBridge.lean
./lean/InfoGeometry/Canonical/AffineOrthogonal55Glide.lean
./lean/InfoGeometry/Canonical/AInfinityAlgebraHigherAssociativity.lean
./lean/InfoGeometry/Canonical/AInftyColimitBoundaryResolution.lean
./lean/InfoGeometry/Canonical/AlgebraicStarEnvelopeNorm.lean
./lean/InfoGeometry/Canonical/AlgebraicStarEnvelopeTopologicalRealization.lean
./lean/InfoGeometry/Canonical/AltlandZirnbauerTenfoldMasterBridge.lean
./lean/InfoGeometry/Canonical/AndreevReflectionKreinHorizonBridge.lean
./lean/InfoGeometry/Canonical/AnosovQuantumErgodicFlowBridge.lean
./lean/InfoGeometry/Canonical/AnyonBraidOperatorMasterBridge.lean
./lean/InfoGeometry/Canonical/AnyonCondensationDomainWallBridge.lean
./lean/InfoGeometry/Canonical/AnyonicStabilizerCodeDistance.lean
./lean/InfoGeometry/Canonical/AnyonYangBaxterBraiding.lean
./lean/InfoGeometry/Canonical/AreaLawEntropyViolationBridge.lean
./lean/InfoGeometry/Canonical/ArtinBraidDeduplicatedMasterBridge.lean
./lean/InfoGeometry/Canonical/AtiyahSingerChiralIndex.lean
./lean/InfoGeometry/Canonical/AtiyahTQFTCobordismBridge.lean
./lean/InfoGeometry/Canonical/AubertPlymen.lean
./lean/InfoGeometry/Canonical/AutoGeneratedKrein.lean
./lean/InfoGeometry/Canonical/AutomorphicSugawaraCalibration.lean
./lean/InfoGeometry/Canonical/BekensteinHolographyNativeBridge.lean
./lean/InfoGeometry/Canonical/BerryHolonomy.lean
./lean/InfoGeometry/Canonical/BinaryModularMoebiusBridge.lean
./lean/InfoGeometry/Canonical/BiquaternionKANnilpotent.lean
./lean/InfoGeometry/Canonical/BiquaternionLaplaceTripotent.lean
./lean/InfoGeometry/Canonical/BiquaternionLorentzPolarBridge.lean
./lean/InfoGeometry/Canonical/BiquaternionNegativeRootsLog.lean
./lean/InfoGeometry/Canonical/BisognanoWichmannUnruhAQFT.lean
./lean/InfoGeometry/Canonical/BMSSymmetrySoftHairBridge.lean
./lean/InfoGeometry/Canonical/BostConnesKTheoryIntegration.lean
./lean/InfoGeometry/Canonical/BostConnesRiemannZetaPhaseTransitionBridge.lean
./lean/InfoGeometry/Canonical/BulgarianThermodynamicGeometryBridge.lean
./lean/InfoGeometry/Canonical/BulgarianThermodynamicGeometryPacket.lean
./lean/InfoGeometry/Canonical/BuresInformationGeodesicFlow.lean
./lean/InfoGeometry/Canonical/BuresMetricClosedCartography.lean
./lean/InfoGeometry/Canonical/CalabiYauGrandDualityBridge.lean
./lean/InfoGeometry/Canonical/CalabiYauMirrorSymmetryBridge.lean
./lean/InfoGeometry/Canonical/CanonicalZornCliffordIsomorphism.lean
./lean/InfoGeometry/Canonical/CanonicalZornCliffordRepresentation.lean
./lean/InfoGeometry/Canonical/CanonicalZornCompositionFiveGradeBridge.lean
./lean/InfoGeometry/Canonical/CanonicalZornCompositionTriality.lean
./lean/InfoGeometry/Canonical/CanonicalZornConformalProjectiveScalingAudit.lean
./lean/InfoGeometry/Canonical/CanonicalZornDiracConnectionRepresentation.lean
./lean/InfoGeometry/Canonical/CanonicalZornFiveGradedClosure.lean
./lean/InfoGeometry/Canonical/CanonicalZornFiveGradeReversal.lean
./lean/InfoGeometry/Canonical/CanonicalZornFiveGradeSymmetryClosure.lean
./lean/InfoGeometry/Canonical/CanonicalZornIntegralSpinRepresentation.lean
./lean/InfoGeometry/Canonical/CanonicalZornIntegralSpinSubgroup.lean
./lean/InfoGeometry/Canonical/CanonicalZornIntegralSpinTrialityClosure.lean
./lean/InfoGeometry/Canonical/CanonicalZornIntegralTrialityEquivariance.lean
./lean/InfoGeometry/Canonical/CanonicalZornNullCliffordClosure.lean
./lean/InfoGeometry/Canonical/CanonicalZornOuterTrialityGroup.lean
./lean/InfoGeometry/Canonical/CanonicalZornProjectiveCore.lean
./lean/InfoGeometry/Canonical/CanonicalZornProjectiveTKKBridge.lean
./lean/InfoGeometry/Canonical/CanonicalZornRealComplexSpinBaseChange.lean
./lean/InfoGeometry/Canonical/CanonicalZornRealSpin44.lean
./lean/InfoGeometry/Canonical/CanonicalZornRealSpinTrialityClosure.lean
./lean/InfoGeometry/Canonical/CanonicalZornSpinChirality.lean
./lean/InfoGeometry/Canonical/CanonicalZornSpinRelatedFiber.lean
./lean/InfoGeometry/Canonical/CanonicalZornUnifiedClosure.lean
./lean/InfoGeometry/Canonical/CantorBoundaryTomitaBridge.lean
./lean/InfoGeometry/Canonical/CantorCoadjointHamiltonianFlowBridge.lean
./lean/InfoGeometry/Canonical/CantorTwoTreeColimitBridge.lean
./lean/InfoGeometry/Canonical/CausalDiracMatrixBasisChange.lean
./lean/InfoGeometry/Canonical/CausalFunctor.lean
./lean/InfoGeometry/Canonical/CausalVortexCooperPairing.lean
./lean/InfoGeometry/Canonical/CausalVortexPauliEigenspaces.lean
./lean/InfoGeometry/Canonical/CausalVortexPauliMajorana.lean
./lean/InfoGeometry/Canonical/CausalVortexPauliPositivity.lean
./lean/InfoGeometry/Canonical/CausalVortexPauliSpectral.lean
./lean/InfoGeometry/Canonical/CelikZ3FibonacciBridge.lean
./lean/InfoGeometry/Canonical/ChernSimonsGaugeInvarianceBridge.lean
./lean/InfoGeometry/Canonical/ChernSimonsKnotInvariant.lean
./lean/InfoGeometry/Canonical/ChiralAnomalyCantor.lean
./lean/InfoGeometry/Canonical/ChiralCuntzSuperchargeBridge.lean
./lean/InfoGeometry/Canonical/ChiralParitySuperalgebra.lean
./lean/InfoGeometry/Canonical/CKWEntanglementMonogamyBridge.lean
./lean/InfoGeometry/Canonical/Cl11DiracOperatorConnection.lean
./lean/InfoGeometry/Canonical/Cl11SheetDiracMatrices.lean
./lean/InfoGeometry/Canonical/Cl11TrifactorSeed.lean
./lean/InfoGeometry/Canonical/Cl11WittBasis.lean
./lean/InfoGeometry/Canonical/Cl44BridgeCandidate.lean
./lean/InfoGeometry/Canonical/Cl55OperatorAlgebraHom.lean
./lean/InfoGeometry/Canonical/Cl55OperatorRingCatColimit.lean
./lean/InfoGeometry/Canonical/CliffordCantorModeHierarchy.lean
./lean/InfoGeometry/Canonical/CliffordInfiniteLimit.lean
./lean/InfoGeometry/Canonical/CliffordInfiniteSplitAlgebra.lean
./lean/InfoGeometry/Canonical/CofinalTailModularFlowTopologicalBridge.lean
./lean/InfoGeometry/Canonical/CofinalTailTomitaGraphTopologicalBridge.lean
./lean/InfoGeometry/Canonical/CompatibleStateColimitTopCatBridge.lean
./lean/InfoGeometry/Canonical/CompatibleStateContinuousReadout.lean
./lean/InfoGeometry/Canonical/ComplexDifferentiableBridge.lean
./lean/InfoGeometry/Canonical/ConcreteCuntzKCommutation.lean
./lean/InfoGeometry/Canonical/ConcreteSuperVirasoroColimitReadback.lean
./lean/InfoGeometry/Canonical/ConformalEngine.lean
./lean/InfoGeometry/Canonical/ConformalProjectiveClosure.lean
./lean/InfoGeometry/Canonical/ConformalSubalgebraDebt.lean
./lean/InfoGeometry/Canonical/ConnesChernCharacterBridge.lean
./lean/InfoGeometry/Canonical/ConnesCocycleLogarithmicDerivative.lean
./lean/InfoGeometry/Canonical/ConnesCyclicCohomology.lean
./lean/InfoGeometry/Canonical/ConnesLodayCyclicComplexBridge.lean
./lean/InfoGeometry/Canonical/ConnesRadonNikodymCocycle.lean
./lean/InfoGeometry/Canonical/ConnesSpectral1FormAlgebra.lean
./lean/InfoGeometry/Canonical/ConnesSpectralMetricBridge.lean
./lean/InfoGeometry/Canonical/ConnesSpectralTripleBridge.lean
./lean/InfoGeometry/Canonical/ConnesTomitaModularAutomorphismBridge.lean
./lean/InfoGeometry/Canonical/ContinuousTraceColimitCocone.lean
./lean/InfoGeometry/Canonical/CStarAlgebraDirectSumBlock.lean
./lean/InfoGeometry/Canonical/CStarAlgebraStateColimit.lean
./lean/InfoGeometry/Canonical/CumulantGeneratingConvexity.lean
./lean/InfoGeometry/Canonical/Cuntz2Isometries.lean
./lean/InfoGeometry/Canonical/CuntzAlgebraO2Noncommutative.lean
./lean/InfoGeometry/Canonical/CuntzKriegerMarkovBridge.lean
./lean/InfoGeometry/Canonical/CuntzNIsometries.lean
./lean/InfoGeometry/Canonical/CuntzStageModularFlowColimitReadout.lean
./lean/InfoGeometry/Canonical/CuntzTomitaTakesaki.lean
./lean/InfoGeometry/Canonical/CuntzWordReduction.lean
./lean/InfoGeometry/Canonical/CyclicCocycleCantor.lean
./lean/InfoGeometry/Canonical/DeformedIdeleActionBridge.lean
./lean/InfoGeometry/Canonical/DeRhamArnoldTwistorPenroseBridge.lean
./lean/InfoGeometry/Canonical/DiscreteFreeEnergyDissipationBridge.lean
./lean/InfoGeometry/Canonical/DiscreteGaussBonnetKleinBridge.lean
./lean/InfoGeometry/Canonical/DModuleLagrangianBridge.lean
./lean/InfoGeometry/Canonical/DoubledFibonacciCondensationBridge.lean
./lean/InfoGeometry/Canonical/DrazinCARColimitBridge_proposal.lean
./lean/InfoGeometry/Canonical/DrinfeldCenterFibonacciBridge.lean
./lean/InfoGeometry/Canonical/E8ExceptionalLieAlgebraTriality.lean
./lean/InfoGeometry/Canonical/E8LeechBridge.lean
./lean/InfoGeometry/Canonical/ErlangenJaynesGromov.lean
./lean/InfoGeometry/Canonical/ETHQuantumThermalizationBridge.lean
./lean/InfoGeometry/Canonical/FedosovStarProductQuantization.lean
./lean/InfoGeometry/Canonical/FibonacciAnyonBraidingBridge.lean
./lean/InfoGeometry/Canonical/FibonacciAnyonModularCategoryBridge.lean
./lean/InfoGeometry/Canonical/FibonacciAnyonSimilarity.lean
./lean/InfoGeometry/Canonical/FibonacciBraidingPhaseBridge.lean
./lean/InfoGeometry/Canonical/FibonacciCentralChargeBridge.lean
./lean/InfoGeometry/Canonical/FibonacciHexagonEquationBridge.lean
./lean/InfoGeometry/Canonical/FibonacciModularGroupBridge.lean
./lean/InfoGeometry/Canonical/FibonacciPentagonEquationBridge.lean
./lean/InfoGeometry/Canonical/FierzModularConjugationBridge.lean
./lean/InfoGeometry/Canonical/FilteredColimitCuntzAlgebraMasterBridge.lean
./lean/InfoGeometry/Canonical/FilteredDirectInverseColimit.lean
./lean/InfoGeometry/Canonical/FilteredDirectLimitHKAnalyticityBridge.lean
./lean/InfoGeometry/Canonical/FilteredDualFunctionalTopologicalLimit.lean
./lean/InfoGeometry/Canonical/FilteredGNSAlgebraicColimitRepresentation.lean
./lean/InfoGeometry/Canonical/FilteredGNSBoundarySpine.lean
./lean/InfoGeometry/Canonical/FilteredGNSBoundedGeneratorUnitaryFlow.lean
./lean/InfoGeometry/Canonical/FilteredGNSCofinalTail.lean
./lean/InfoGeometry/Canonical/FilteredGNSCofinalTailTopCatEquivalence.lean
./lean/InfoGeometry/Canonical/FilteredGNSCofinalTailTopological.lean
./lean/InfoGeometry/Canonical/FilteredGNSCofinalTailTopology.lean
./lean/InfoGeometry/Canonical/FilteredGNSColimitRepresentation.lean
./lean/InfoGeometry/Canonical/FilteredGNSCompletionKMSState.lean
./lean/InfoGeometry/Canonical/FilteredGNSFaithfulAlgebraicQuotient.lean
./lean/InfoGeometry/Canonical/FilteredGNSFaithfulCStarRepresentation.lean
./lean/InfoGeometry/Canonical/FilteredGNSFaithfulRangeQuotient.lean
./lean/InfoGeometry/Canonical/FilteredGNSGlobalRepresentationCompatibility.lean
./lean/InfoGeometry/Canonical/FilteredGNSGlobalStageRepresentation.lean
./lean/InfoGeometry/Canonical/FilteredGNSGlobalStageRepresentationTransport.lean
./lean/InfoGeometry/Canonical/FilteredGNSHilbertColimit.lean
./lean/InfoGeometry/Canonical/FilteredGNSHilbertColimitTopology.lean
./lean/InfoGeometry/Canonical/FilteredGNSHilbertNontrivial.lean
./lean/InfoGeometry/Canonical/FilteredGNSHilbertTopologicalColimitDenseRange.lean
./lean/InfoGeometry/Canonical/FilteredGNSNormPullbackBinding.lean
./lean/InfoGeometry/Canonical/FilteredGNSOperatorConjugationTopCat.lean
./lean/InfoGeometry/Canonical/FilteredGNSOperatorSeminormKernel.lean
./lean/InfoGeometry/Canonical/FilteredGNSRepresentation.lean
./lean/InfoGeometry/Canonical/FilteredGNSRepresentationTopologicalInstantiation.lean
./lean/InfoGeometry/Canonical/FilteredGNSRepresentedAlgebraCompletion.lean
./lean/InfoGeometry/Canonical/FilteredGNSRepresentedCompletionModularTransport.lean
./lean/InfoGeometry/Canonical/FilteredGNSRepresentedCStarClosure.lean
./lean/InfoGeometry/Canonical/FilteredGNSRepresentedCStarCompletion.lean
./lean/InfoGeometry/Canonical/FilteredGNSRepresentedCStarModularAutomorphism.lean
./lean/InfoGeometry/Canonical/FilteredGNSRepresentedCStarStateCompletion.lean
./lean/InfoGeometry/Canonical/FilteredGNSRepresentedCStarTopCatEquivalence.lean
./lean/InfoGeometry/Canonical/FilteredGNSRepresentedCStarTopology.lean
./lean/InfoGeometry/Canonical/FilteredGNSRepresentedRangeCompletion.lean
./lean/InfoGeometry/Canonical/FilteredGNSTailRepresentation.lean
./lean/InfoGeometry/Canonical/FilteredGNSTailRepresentationTopology.lean
./lean/InfoGeometry/Canonical/FilteredGNSTailStarRepresentation.lean
./lean/InfoGeometry/Canonical/FilteredGNSTomitaClosability.lean
./lean/InfoGeometry/Canonical/FilteredGNSTomitaClosedOperator.lean
./lean/InfoGeometry/Canonical/FilteredGNSTomitaClosedTransport.lean
./lean/InfoGeometry/Canonical/FilteredGNSTomitaComplexColimit.lean
./lean/InfoGeometry/Canonical/FilteredGNSTomitaCore.lean
./lean/InfoGeometry/Canonical/FilteredGNSTomitaDomainColimit.lean
./lean/InfoGeometry/Canonical/FilteredGNSTomitaDomainTopologicalColimit.lean
./lean/InfoGeometry/Canonical/FilteredGNSTomitaGraphClosure.lean
./lean/InfoGeometry/Canonical/FilteredGNSTomitaGraphTopologicalColimit.lean
./lean/InfoGeometry/Canonical/FilteredGNSTomitaModularFormColimit.lean
./lean/InfoGeometry/Canonical/FilteredGNSTomitaModularForm.lean
./lean/InfoGeometry/Canonical/FilteredGNSTomitaModularHilbertCompletion.lean
./lean/InfoGeometry/Canonical/FilteredGNSTomitaModularQuotient.lean
./lean/InfoGeometry/Canonical/FilteredGNSTomitaRealColimit.lean
./lean/InfoGeometry/Canonical/FilteredInductiveColimitBottPeriodicityBridge.lean
./lean/InfoGeometry/Canonical/FilteredInductiveColimitHestenesKreinSynthesisBridge.lean
./lean/InfoGeometry/Canonical/FilteredStarAlgebraActionDirectLimit.lean
./lean/InfoGeometry/Canonical/FilteredStarAlgebraActionEquivDirectLimit.lean
./lean/InfoGeometry/Canonical/FilteredStarAlgebraActionEquivTopologicalCompatibility.lean
./lean/InfoGeometry/Canonical/FilteredStarAlgebraActionTopologicalCompatibility.lean
./lean/InfoGeometry/Canonical/FilteredStarAlgebraAlgebraicToTopologicalColimit.lean
./lean/InfoGeometry/Canonical/FilteredStarAlgebraDirectLimit.lean
./lean/InfoGeometry/Canonical/FilteredStarAlgebraDirectLimitTopologicalCompatibility.lean
./lean/InfoGeometry/Canonical/FilteredStarAlgebraDirectLimitTopologicalRealization.lean
./lean/InfoGeometry/Canonical/FilteredStarAlgebraFiniteGroupActionDirectLimit.lean
./lean/InfoGeometry/Canonical/FilteredStarAlgebraFiniteGroupActionEquivDirectLimit.lean
./lean/InfoGeometry/Canonical/FilteredStarAlgebraFiniteGroupActionTopologicalCompatibility.lean
./lean/InfoGeometry/Canonical/FilteredStarAlgebraTopologicalRepresentationFlow.lean
./lean/InfoGeometry/Canonical/FilteredStarAlgebraTopologicalRepresentationTransport.lean
./lean/InfoGeometry/Canonical/FilteredStarAlgebraTopologicalStarReadout.lean
./lean/InfoGeometry/Canonical/FilteredStarAlgebraTopologicalTraceTransport.lean
./lean/InfoGeometry/Canonical/FilteredStarInductiveCoconeTopCat.lean
./lean/InfoGeometry/Canonical/FilteredStarInductiveSystemTopCat.lean
./lean/InfoGeometry/Canonical/FilteredTopologicalDirectInverseColimit.lean
./lean/InfoGeometry/Canonical/FiniteFibonacciQubitNoLeakageBridge.lean
./lean/InfoGeometry/Canonical/FiniteGibbsQGTBridge.lean
./lean/InfoGeometry/Canonical/FiniteInformationGeometryArchitecture.lean
./lean/InfoGeometry/Canonical/FinitePhenomenologyReadout.lean
./lean/InfoGeometry/Canonical/FormalVerificationPacket.lean
./lean/InfoGeometry/Canonical/Foundations.lean
./lean/InfoGeometry/Canonical/FQHEChiralEdgeCFTBridge.lean
./lean/InfoGeometry/Canonical/FQHEMooreReadPfaffianBridge.lean
./lean/InfoGeometry/Canonical/FractalCantorMoebiusLorentzBogoliubovBridge.lean
./lean/InfoGeometry/Canonical/FractionalAnyonTopologicalSpin.lean
./lean/InfoGeometry/Canonical/FrechetCliffordOperatorFormBridge.lean
./lean/InfoGeometry/Canonical/FreeEnergyDissipationRate.lean
./lean/InfoGeometry/Canonical/FreeEnergyEquilibriumUnitaryBridge.lean
./lean/InfoGeometry/Canonical/FullOperatorBKMQuantumFisher.lean
./lean/InfoGeometry/Canonical/Geometry.lean
./lean/InfoGeometry/Canonical/GlobalBostConnesFactorizationBridge.lean
./lean/InfoGeometry/Canonical/GottesmanKnillStabilizerCodeBridge.lean
./lean/InfoGeometry/Canonical/GrandSynthesis.lean
./lean/InfoGeometry/Canonical/GromovWittenPrepotential.lean
./lean/InfoGeometry/Canonical/GrothendieckGroup.lean
./lean/InfoGeometry/Canonical/HaagerupSubfactorAnyonBridge.lean
./lean/InfoGeometry/Canonical/HaagKastlerReehSchliederAQFT.lean
./lean/InfoGeometry/Canonical/HaPPYPerfectTensorHolography.lean
./lean/InfoGeometry/Canonical/HessianGeometry.lean
./lean/InfoGeometry/Canonical/HestenesBivectorBracket.lean
./lean/InfoGeometry/Canonical/HestenesBivectorCarrierTest10.lean
./lean/InfoGeometry/Canonical/HestenesBivectorCarrierTest3.lean
./lean/InfoGeometry/Canonical/HestenesBivectorCarrierTest4.lean
./lean/InfoGeometry/Canonical/HestenesBivectorCarrierTest5.lean
./lean/InfoGeometry/Canonical/HestenesBivectorCarrierTest6.lean
./lean/InfoGeometry/Canonical/HestenesBivectorCarrierTest7.lean
./lean/InfoGeometry/Canonical/HestenesBivectorCarrierTest8.lean
./lean/InfoGeometry/Canonical/HestenesKreinAnalyticFrontierColimit.lean
./lean/InfoGeometry/Canonical/HestenesKreinBoundaryScatteringColimit.lean
./lean/InfoGeometry/Canonical/HestenesKreinCompletionChannelsColimit.lean
./lean/InfoGeometry/Canonical/HilbertSchmidtMatrixPairing.lean
./lean/InfoGeometry/Canonical/HolevoQuantityChannelCapacityBridge.lean
./lean/InfoGeometry/Canonical/HolographicBekensteinHawkingUnruh.lean
./lean/InfoGeometry/Canonical/HolographicComplexityKreinBridge.lean
./lean/InfoGeometry/Canonical/HorizonZitterFierzReadback.lean
./lean/InfoGeometry/Canonical/HurwitzZeroTransferTheoremContractBridge.lean
./lean/InfoGeometry/Canonical/InductiveOperatorTaylorClosure.lean
./lean/InfoGeometry/Canonical/InfiniteColimitExtensionIsomorphismBridge.lean
./lean/InfoGeometry/Canonical/InfoGeometryUnification.lean
./lean/InfoGeometry/Canonical/IntegralZornBilinearComposition.lean
./lean/InfoGeometry/Canonical/IntegralZornCompositionAlgebra.lean
./lean/InfoGeometry/Canonical/IntegralZornII44Bridge.lean
./lean/InfoGeometry/Canonical/ItakuraSaitoCuntzBridge.lean
./lean/InfoGeometry/Canonical/JackiwTeitelboimDilatonBridge.lean
./lean/InfoGeometry/Canonical/JarzynskiQuantumThermodynamicsBridge.lean
./lean/InfoGeometry/Canonical/JaynesFormalism.lean
./lean/InfoGeometry/Canonical/JordanWignerCelikKocakBridgeNDepth_proposal.lean
./lean/InfoGeometry/Canonical/K0Functor.lean
./lean/InfoGeometry/Canonical/KacMoodyCurrentAlgebraBridge.lean
./lean/InfoGeometry/Canonical/KadisonSingerStateExtension.lean
./lean/InfoGeometry/Canonical/KasparovKHomologyProductBridge.lean
./lean/InfoGeometry/Canonical/KasparovKKTheoryBivariantBridge.lean
./lean/InfoGeometry/Canonical/KitaevBdGPfaffianBridge.lean
./lean/InfoGeometry/Canonical/KitaevChainTopologicalZ2Invariant.lean
./lean/InfoGeometry/Canonical/KitaevCliffordBridge.lean
./lean/InfoGeometry/Canonical/KitaevCuntzCliffordBridge.lean
./lean/InfoGeometry/Canonical/KitaevHoneycombPlaquetteFluxBridge.lean
./lean/InfoGeometry/Canonical/KitaevQuantumDoubleGSDBridge.lean
./lean/InfoGeometry/Canonical/KitaevSpinLiquidHoneycombBridge.lean
./lean/InfoGeometry/Canonical/KleinBottleMoebiusToricCodeBridge.lean
./lean/InfoGeometry/Canonical/KleinBottleSewing.lean
./lean/InfoGeometry/Canonical/KleinQuadric.lean
./lean/InfoGeometry/Canonical/KleinSpinorOrbitMasterBridge.lean
./lean/InfoGeometry/Canonical/KLinearGap.lean
./lean/InfoGeometry/Canonical/KMSBoundaryTrajectory.lean
./lean/InfoGeometry/Canonical/KMSInteriorPoint.lean
./lean/InfoGeometry/Canonical/KrDualityCascade.lean
./lean/InfoGeometry/Canonical/KreinCarrierInstances/Bridge.lean
./lean/InfoGeometry/Canonical/KreinCarrierInstances/Carrier.lean
./lean/InfoGeometry/Canonical/KreinCarrierInstances/CoreProjector.lean
./lean/InfoGeometry/Canonical/KreinCarrierInstances/Datum.lean
./lean/InfoGeometry/Canonical/KreinCarrierInstances.lean
./lean/InfoGeometry/Canonical/KreinCarrierInstances/RelativeFredholm.lean
./lean/InfoGeometry/Canonical/KreinCarrierInstances/RotorFlow.lean
./lean/InfoGeometry/Canonical/KuboMoriBogoliubovMetric.lean
./lean/InfoGeometry/Canonical/KuzminFockSpaceAnyon.lean
./lean/InfoGeometry/Canonical/LaughlinStateQuantumHallBridge.lean
./lean/InfoGeometry/Canonical/LevinWenStringNetTopologicalEntropy.lean
./lean/InfoGeometry/Canonical/LiHaldaneEntanglementSpectrumBridge.lean
./lean/InfoGeometry/Canonical/LogarithmicDerivativeBridge.lean
./lean/InfoGeometry/Canonical/MadelungAnscombeAmplitudeWaveBridge.lean
./lean/InfoGeometry/Canonical/MajoranaBraidingCliffordBridge.lean
./lean/InfoGeometry/Canonical/MajoranaZeroModeParity.lean
./lean/InfoGeometry/Canonical/MasterSynthesis.lean
./lean/InfoGeometry/Canonical/MatrixAlgebraCuntzEmbedding.lean
./lean/InfoGeometry/Canonical/MERATensorNetworkHolographyBridge.lean
./lean/InfoGeometry/Canonical/MetriplecticCriticalFlowBridge.lean
./lean/InfoGeometry/Canonical/MetriplecticDissipativeSystem.lean
./lean/InfoGeometry/Canonical/MetriplecticZetaResonance.lean
./lean/InfoGeometry/Canonical/MicrocanonicalBoltzmann.lean
./lean/InfoGeometry/Canonical/ModularEvolution.lean
./lean/InfoGeometry/Canonical/ModularGibbsColimitBridge.lean
./lean/InfoGeometry/Canonical/ModularLogGenerating.lean
./lean/InfoGeometry/Canonical/ModularSpectralAsymmetryBridge.lean
./lean/InfoGeometry/Canonical/ModularSpinorCantorCl11LimitBridge.lean
./lean/InfoGeometry/Canonical/ModularSpinorCantorProjectiveBernoulliMeasureBridge.lean
./lean/InfoGeometry/Canonical/ModularSpinorCantorProjectiveBranchReadoutBridge.lean
./lean/InfoGeometry/Canonical/ModularSpinorCantorProjectiveInverseLimitReadoutBridge.lean
./lean/InfoGeometry/Canonical/ModularSpinorCantorProjectiveReadoutBridge.lean
./lean/InfoGeometry/Canonical/ModularSpinorCl11MarkovJonesTopologicalColimitBridge.lean
./lean/InfoGeometry/Canonical/ModularSpinorCl11MarkovJonesTopologicalCyclicBridge.lean
./lean/InfoGeometry/Canonical/ModularSpinorCuntzStageColimitBridge.lean
./lean/InfoGeometry/Canonical/ModularSpinorCuntzStageTopologicalIsoBridge.lean
./lean/InfoGeometry/Canonical/ModularSpinorCuntzStageTopologicalRepresentationBridge.lean
./lean/InfoGeometry/Canonical/ModularTomitaGeometry.lean
./lean/InfoGeometry/Canonical/ModularZ2CubeGrading.lean
./lean/InfoGeometry/Canonical/MoebiusHurwitzDuality.lean
./lean/InfoGeometry/Canonical/MoebiusVirasoroBridge.lean
./lean/InfoGeometry/Canonical/Monotonicity.lean
./lean/InfoGeometry/Canonical/MontonenOliveSDualityDiracQuantization.lean
./lean/InfoGeometry/Canonical/MooreReadPfaffianFractionalHall.lean
./lean/InfoGeometry/Canonical/MultiChainUHFEmbedding.lean
./lean/InfoGeometry/Canonical/NambuGorkovParticleHoleBridge.lean
./lean/InfoGeometry/Canonical/NaryToeplitzWeightedTripotent.lean
./lean/InfoGeometry/Canonical/NeutralDualPair.lean
./lean/InfoGeometry/Canonical/NeutralDualPairSpinorBridge.lean
./lean/InfoGeometry/Canonical/NonAbelianBerryPhaseBridge.lean
./lean/InfoGeometry/Canonical/NonAbelianGaugeBianchiIdentity.lean
./lean/InfoGeometry/Canonical/NonCommutativeJordanAlgebra.lean
./lean/InfoGeometry/Canonical/NoncommutativeOperatorAlgebra.lean
./lean/InfoGeometry/Canonical/NoncommutativeTorusAlgebraBridge.lean
./lean/InfoGeometry/Canonical/NonCommutativeTorusMoritaBridge.lean
./lean/InfoGeometry/Canonical/NormalConeInductive.lean
./lean/InfoGeometry/Canonical/NormalizedTraceCauchySchwarz.lean
./lean/InfoGeometry/Canonical/NormalizedTraceCyclicity.lean
./lean/InfoGeometry/Canonical/NormalizedTraceInvariance.lean
./lean/InfoGeometry/Canonical/NormalizedTracePositivity.lean
./lean/InfoGeometry/Canonical/OperatorGradedAdjointLift.lean
./lean/InfoGeometry/Canonical/OperatorPin55Action.lean
./lean/InfoGeometry/Canonical/OperatorTKKAnomalyAnnihilation.lean
./lean/InfoGeometry/Canonical/OTOCScramblingChaosBridge.lean
./lean/InfoGeometry/Canonical/PeirceDeWittIdealModularBridge.lean
./lean/InfoGeometry/Canonical/_PeirceScratch.lean
./lean/InfoGeometry/Canonical/PenroseTwistor.lean
./lean/InfoGeometry/Canonical/PhysicalBdGPairingBridge.lean
./lean/InfoGeometry/Canonical/Positivity.lean
./lean/InfoGeometry/Canonical/PowerVarianceGeometry.lean
./lean/InfoGeometry/Canonical/PrimeCocycleCoefficients.lean
./lean/InfoGeometry/Canonical/PrimeExteriorRepresentationCalibration.lean
./lean/InfoGeometry/Canonical/PrimeLeeYangThermodynamicLimitMasterBridge.lean
./lean/InfoGeometry/Canonical/PrimeMajoranaWittenCharacter.lean
./lean/InfoGeometry/Canonical/PrimeWittenCharacterCalibration.lean
./lean/InfoGeometry/Canonical/ProjectedLFunctionCalibration.lean
./lean/InfoGeometry/Canonical/ProjectiveAffineConformalClosure55.lean
./lean/InfoGeometry/Canonical/ProjectiveCCR.lean
./lean/InfoGeometry/Canonical/ProofDAGRepresentationBridge.lean
./lean/InfoGeometry/Canonical/ProofGraphExteriorCalculusBridge.lean
./lean/InfoGeometry/Canonical/QuantumChannelContractivity.lean
./lean/InfoGeometry/Canonical/QuantumDoubleS3Bridge.lean
./lean/InfoGeometry/Canonical/QuantumDoubleToricCodeBridge.lean
./lean/InfoGeometry/Canonical/QuantumGroupHopfAlgebra.lean
./lean/InfoGeometry/Canonical/QuantumGroupUqSL2Bridge.lean
./lean/InfoGeometry/Canonical/QuantumHallChernNumber.lean
./lean/InfoGeometry/Canonical/QuantumHallSkyrmionBridge.lean
./lean/InfoGeometry/Canonical/QuantumHallSkyrmionTopologicalCharge.lean
./lean/InfoGeometry/Canonical/QuantumInformationBottleneckBridge.lean
./lean/InfoGeometry/Canonical/QuantumRelativeEntropyMonotonicity.lean
./lean/InfoGeometry/Canonical/QuantumRelativeSurprisal.lean
./lean/InfoGeometry/Canonical/QuantumTransportCoefficientBridge.lean
./lean/InfoGeometry/Canonical/RealComplexRotorHomeomorph.lean
./lean/InfoGeometry/Canonical/RealDoubledChiralKreinBridge.lean
./lean/InfoGeometry/Canonical/RealSplitOctFiveGradeProjectiveBridge.lean
./lean/InfoGeometry/Canonical/RenyiFromModularPowers.lean
./lean/InfoGeometry/Canonical/RenyiRelativeEntropy.lean
./lean/InfoGeometry/Canonical/Sandbox/QuantumGrassmannian.lean
./lean/InfoGeometry/Canonical/SE2CompactAffineOrbit.lean
./lean/InfoGeometry/Canonical/SE2SouriauCoadjointOrbit.lean
./lean/InfoGeometry/Canonical/SE2SouriauCoadjointTopology.lean
./lean/InfoGeometry/Canonical/SE2SouriauCompactOrbit.lean
./lean/InfoGeometry/Canonical/SeibergWittenGaugeMapBridge.lean
./lean/InfoGeometry/Canonical/SelfDualWeylKleinBridge.lean
./lean/InfoGeometry/Canonical/SimplexSurprisalMetriplectic.lean
./lean/InfoGeometry/Canonical/SingularityCausalCoupling.lean
./lean/InfoGeometry/Canonical/SkyrmionPontryaginTopologicalChargeBridge.lean
./lean/InfoGeometry/Canonical/SL2RToG2WiesbrockEmbedding.lean
./lean/InfoGeometry/Canonical/S_left_K_commutation.lean
./lean/InfoGeometry/Canonical/SolderingQuaternionicGaugeBianchiBridge.lean
./lean/InfoGeometry/Canonical/SouriauBregmanLegendreBridge.lean
./lean/InfoGeometry/Canonical/SouriauBuresWassersteinBridge.lean
./lean/InfoGeometry/Canonical/SouriauCoadjointCovariance.lean
./lean/InfoGeometry/Canonical/SouriauCoadjointFisherRaoEquivalence.lean
./lean/InfoGeometry/Canonical/SouriauCoadjointOrbitSymplecticReduction.lean
./lean/InfoGeometry/Canonical/SouriauHellingerSquareRootBridge.lean
./lean/InfoGeometry/Canonical/SouriauHilbertSchmidtOnsager.lean
./lean/InfoGeometry/Canonical/SouriauInformationCurvatureTensor.lean
./lean/InfoGeometry/Canonical/SouriauKahlerCoadjointBridge.lean
./lean/InfoGeometry/Canonical/SouriauKKSForm.lean
./lean/InfoGeometry/Canonical/SouriauMetriplecticBracket.lean
./lean/InfoGeometry/Canonical/SouriauOnsagerBKMBridge.lean
./lean/InfoGeometry/Canonical/SouriauOnsagerBKMIntegrabilityAdapter.lean
./lean/InfoGeometry/Canonical/SouriauOnsagerBKMIntegrability.lean
./lean/InfoGeometry/Canonical/SouriauOnsagerBKMRealForm.lean
./lean/InfoGeometry/Canonical/SouriauQuantumCramerRaoHelstromBridge.lean
./lean/InfoGeometry/Canonical/SouriauRelativeEntropyBandTopology.lean
./lean/InfoGeometry/Canonical/SouriauRelativeEntropyFisherBridge.lean
./lean/InfoGeometry/Canonical/SouriauRelativeEntropyLevelTopology.lean
./lean/InfoGeometry/Canonical/SouriauRelativeEntropyPersistenceBifiltration.lean
./lean/InfoGeometry/Canonical/SouriauRelativeEntropyPersistenceColimit.lean
./lean/InfoGeometry/Canonical/SouriauRelativeEntropyPersistenceComparisonIndependence.lean
./lean/InfoGeometry/Canonical/SouriauRelativeEntropyPersistenceCutoffFunctor.lean
./lean/InfoGeometry/Canonical/SouriauRelativeEntropyPersistenceCutoff.lean
./lean/InfoGeometry/Canonical/SouriauRelativeEntropyPersistenceCutoffLimit.lean
./lean/InfoGeometry/Canonical/SouriauRelativeEntropyPersistenceDiagram.lean
./lean/InfoGeometry/Canonical/SouriauRelativeEntropyPersistenceFunctor.lean
./lean/InfoGeometry/Canonical/SouriauRelativeEntropyPersistenceLimitColimitComparison.lean
./lean/InfoGeometry/Canonical/SouriauRelativeEntropyPersistenceMixedComparison.lean
./lean/InfoGeometry/Canonical/SouriauRelativeEntropyPersistenceQuotient.lean
./lean/InfoGeometry/Canonical/SouriauRelativeEntropyPersistenceUniversal.lean
./lean/InfoGeometry/Canonical/SouriauRelativeEntropySimplexTopology.lean
./lean/InfoGeometry/Canonical/SouriauRelativeEntropySublevelDiagram.lean
./lean/InfoGeometry/Canonical/SouriauRelativeEntropySublevelTopology.lean
./lean/InfoGeometry/Canonical/SouriauWassersteinGradientFlow.lean
./lean/InfoGeometry/Canonical/SplitOctonionAlternativeLaws.lean
./lean/InfoGeometry/Canonical/SplitOctonionConjugation.lean
./lean/InfoGeometry/Canonical/SplitOctonionCuntzMasterBridge.lean
./lean/InfoGeometry/Canonical/SplitOctonionDoubledLoxodromic.lean
./lean/InfoGeometry/Canonical/SplitOctonionDoubledLoxodromicSpectral.lean
./lean/InfoGeometry/Canonical/SplitOctonionExpLog.lean
./lean/InfoGeometry/Canonical/SplitOctonionHyperbolicFunctionalCalculus.lean
./lean/InfoGeometry/Canonical/SplitOctonionHyperbolicPolarStructure.lean
./lean/InfoGeometry/Canonical/SplitOctonionHyperbolicSpectralProjectors.lean
./lean/InfoGeometry/Canonical/SplitOctonionLoxodromicCircularBridge.lean
./lean/InfoGeometry/Canonical/SplitOctonionPolarTransport.lean
./lean/InfoGeometry/Canonical/SplitOctonionQuaternionChart.lean
./lean/InfoGeometry/Canonical/SplitOctonionQuaternionPolar.lean
./lean/InfoGeometry/Canonical/SplitOctonionRegularEllipticOperators.lean
./lean/InfoGeometry/Canonical/SplitOctonionRegularNormOperators.lean
./lean/InfoGeometry/Canonical/SplitOctonionRegularOperators.lean
./lean/InfoGeometry/Canonical/SplitOctonionRegularParabolicOperators.lean
./lean/InfoGeometry/Canonical/SplitOctonionRegularProjectors.lean
./lean/InfoGeometry/Canonical/SplitOctonionSymplecticDeterminantMasterBridge.lean
./lean/InfoGeometry/Canonical/SplitQuaternionCayleyZornBridge.lean
./lean/InfoGeometry/Canonical/SplitQuaternionConcrete.lean
./lean/InfoGeometry/Canonical/StarAlgEquivPullback.lean
./lean/InfoGeometry/Canonical/StarAlgEquivTransport.lean
./lean/InfoGeometry/Canonical/StoneCantorMathlibPR.lean
./lean/InfoGeometry/Canonical/StoneCantorMathlibScratch.lean
./lean/InfoGeometry/Canonical/StoneDualityBooleanEval.lean
./lean/InfoGeometry/Canonical/SuperKaehlerGromovWittenBridge.lean
./lean/InfoGeometry/Canonical/SuperMetriplecticD4ParityMasterBridge.lean
./lean/InfoGeometry/Canonical/SYKQuantumScramblingBridge.lean
./lean/InfoGeometry/Canonical/TemperleyLiebJonesBridge.lean
./lean/InfoGeometry/Canonical/TensorNetworkHolography.lean
./lean/InfoGeometry/Canonical/TensorTowerColimit.lean
./lean/InfoGeometry/Canonical/TestRing.lean
./lean/InfoGeometry/Canonical/TestScratch.lean
./lean/InfoGeometry/Canonical/TestSplitQ.lean
./lean/InfoGeometry/Canonical/TFDCartanAudit.lean
./lean/InfoGeometry/Canonical/TFDNilpotentCartanAudit.lean
./lean/InfoGeometry/Canonical/TFDNilpotentCartanAudit_user.lean
./lean/InfoGeometry/Canonical/ThermofieldDoubleFreeEnergyEntropy.lean
./lean/InfoGeometry/Canonical/ThirdOrderScalarReadout.lean
./lean/InfoGeometry/Canonical/TKKJordanPairData.lean
./lean/InfoGeometry/Canonical/TomitaConnesBridge.lean
./lean/InfoGeometry/Canonical/TomitaDissipativeBreak.lean
./lean/InfoGeometry/Canonical/TomitaTakesakiKMSEntropyBracket.lean
./lean/InfoGeometry/Canonical/TomitaTakesakiModularCocycle.lean
./lean/InfoGeometry/Canonical/TomitaTakesakiTFDModularOperator.lean
./lean/InfoGeometry/Canonical/TomitaTakesakiWiesbrockZornBridge.lean
./lean/InfoGeometry/Canonical/TopologicalEntanglementEntropyBridge.lean
./lean/InfoGeometry/Canonical/TopologicalInsulatorZ2Bridge.lean
./lean/InfoGeometry/Canonical/TopologicalModularFormsEllipticGenera.lean
./lean/InfoGeometry/Canonical/ToricCodeTwistDefectIsingBridge.lean
./lean/InfoGeometry/Canonical/TripotentFiveGradingDecomposition.lean
./lean/InfoGeometry/Canonical/TripotentHorizonFibonacciBraidCapstoneBridge.lean
./lean/InfoGeometry/Canonical/TripotentLeftRightPeirceProjectors.lean
./lean/InfoGeometry/Canonical/UHFColimitSuperchargeBridge.lean
./lean/InfoGeometry/Canonical/UHFColimitTKKAnomalyBridge.lean
./lean/InfoGeometry/Canonical/UHFDirectLimitCARAlgebra.lean
./lean/InfoGeometry/Canonical/UnitTraceNormalization.lean
./lean/InfoGeometry/Canonical/VerlindeFormulaFibonacciBridge.lean
./lean/InfoGeometry/Canonical/ViazovskaMagicFunctionBridge.lean
./lean/InfoGeometry/Canonical/WessZuminoGaugeConsistency.lean
./lean/InfoGeometry/Canonical/WessZuminoWittenAnomalyBridge.lean
./lean/InfoGeometry/Canonical/WeylCantorCrystal.lean
./lean/InfoGeometry/Canonical/WeylCantorSynthesis.lean
./lean/InfoGeometry/Canonical/WeylIntegrationFixedPoint.lean
./lean/InfoGeometry/Canonical/WeylIntegrationFromPillars.lean
./lean/InfoGeometry/Canonical/WiesbrockLieBracketCommutator.lean
./lean/InfoGeometry/Canonical/WiesbrockSUSYPoincareBridge.lean
./lean/InfoGeometry/Canonical/ZornCartanTorusLaplaceMellin.lean
./lean/InfoGeometry/Canonical/ZornCayleyDicksonIsomorphism.lean
./lean/InfoGeometry/Canonical/ZornCellComposition.lean
./lean/InfoGeometry/Canonical/ZornCore.lean
./lean/InfoGeometry/Canonical/ZornOctonionAnyonGellMannBridge.lean
./lean/InfoGeometry/Canonical/ZornOuterTrialityGroup.lean
./lean/InfoGeometry/Canonical/ZornSuperchargeBoundaryCommutantBridge.lean
./lean/InfoGeometry/Canonical/ZornTrialityTKKBridge.lean
./lean/InfoGeometry/Carrier/All.lean
./lean/InfoGeometry/Carrier/CliffordAction.lean
./lean/InfoGeometry/Categorical/All.lean
./lean/InfoGeometry/Categorical/CelikZ3BraidedTensorBridge.lean
./lean/InfoGeometry/Categorical/CFTBlocks.lean
./lean/InfoGeometry/Categorical/CFTBpz.lean
./lean/InfoGeometry/Categorical/CFTFusion.lean
./lean/InfoGeometry/Categorical/CFTLiouville.lean
./lean/InfoGeometry/Categorical/CFTLogarithmic.lean
./lean/InfoGeometry/Categorical/CFTMinimal.lean
./lean/InfoGeometry/Categorical/CFTPrimary.lean
./lean/InfoGeometry/Categorical/CFTStructure.lean
./lean/InfoGeometry/Categorical/CFTVirasoro.lean
./lean/InfoGeometry/Categorical/CFTWard.lean
./lean/InfoGeometry/Categorical/FibonacciUniversalityColimit.lean
./lean/InfoGeometry/Categorical/FilteredDirectLimitOwner.lean
./lean/InfoGeometry/Categorical/GromovPositiveCone.lean
./lean/InfoGeometry/Categorical/InfinityTopos.lean
./lean/InfoGeometry/Categorical/MobiusGeometry.lean
./lean/InfoGeometry/Categorical/StateSpaceColimitCommutativity.lean
./lean/InfoGeometry/Categorical/ThermodynamicLimitColimit.lean
./lean/InfoGeometry/Categorical/ZornBraidColimitBCFW.lean
./lean/InfoGeometry/Categorical/ZornBraidColimitKMS.lean
./lean/InfoGeometry/Causal/Algebra.lean
./lean/InfoGeometry/Clifford/CliffordInjectivity.lean
./lean/InfoGeometry/Clifford/Hestenes1975.lean
./lean/InfoGeometry/Clifford/QuadraticPolarBridge.lean
./lean/InfoGeometry/Clifford/SpinorRep_REAL.lean
./lean/InfoGeometry/Compatibility/All.lean
./lean/InfoGeometry/CompleteUnifiedBundle.lean
./lean/InfoGeometry/Complex/BergmanKernelLocalization.lean
./lean/InfoGeometry/Core/Jordan.lean
./lean/InfoGeometry/CoverageClosure.lean
./lean/InfoGeometry/DeterminantTrifactor.lean
./lean/InfoGeometry/ErlangenCoordinateless.lean
./lean/InfoGeometry/Eval/SeedProverSmoke.lean
./lean/InfoGeometry/Experimental/WeylCantorFock.lean
./lean/InfoGeometry/Experimental/WeylIntegrationFormula.lean
./lean/InfoGeometry/ExponentialFamily/Analytic/LogSumExp.lean
./lean/InfoGeometry/External/Auto/A35MirrorNuclei.lean
./lean/InfoGeometry/External/Auto/A47KIsospinMixing.lean
./lean/InfoGeometry/External/Auto/A47MirrorNuclei.lean
./lean/InfoGeometry/External/Auto/A67MirrorE1.lean
./lean/InfoGeometry/External/Auto/AdelicDiracOperator.lean
./lean/InfoGeometry/External/Auto/AffineDynkinGoutevTonev.lean
./lean/InfoGeometry/External/Auto/AlgebraicCuntzToeplitzInductive.lean
./lean/InfoGeometry/External/Auto/AmariChentsovFierzTorsion.lean
./lean/InfoGeometry/External/Auto/AnomalousKMSFlow.lean
./lean/InfoGeometry/External/Auto/AnomalyInverses.lean
./lean/InfoGeometry/External/Auto/ArangoBrainMetaprogram.lean
./lean/InfoGeometry/External/Auto/ArithmeticHamiltonianZeta.lean
./lean/InfoGeometry/External/Auto/AssociativeCommutatorLie.lean
./lean/InfoGeometry/External/Auto/ASTExtractor.lean
./lean/InfoGeometry/External/Auto/AttentionBirkhoffDecomposition.lean
./lean/InfoGeometry/External/Auto/AttentionBirkhoffGeneral.lean
./lean/InfoGeometry/External/Auto/B3RepresentationBridge.lean
./lean/InfoGeometry/External/Auto/BiquaternionCliffordIso.lean
./lean/InfoGeometry/External/Auto/BiquaternionExpClosure.lean
./lean/InfoGeometry/External/Auto/BiquaternionKANnilpotent.lean
./lean/InfoGeometry/External/Auto/BiquaternionLaplaceTripotent.lean
./lean/InfoGeometry/External/Auto/BiquaternionMobiusSquashing.lean
./lean/InfoGeometry/External/Auto/BiquaternionNegativeRootsLog.lean
./lean/InfoGeometry/External/Auto/BirkhoffInformationGeometry.lean
./lean/InfoGeometry/External/Auto/BisoiForbiddenE1Mixing.lean
./lean/InfoGeometry/External/Auto/BizzetiA67IVGMR.lean
./lean/InfoGeometry/External/Auto/BlackHoleHolography.lean
./lean/InfoGeometry/External/Auto/BM1MirrorNuclei.lean
./lean/InfoGeometry/External/Auto/BogoliubovBraidGraphWeld.lean
./lean/InfoGeometry/External/Auto/BosonicPrimonPartition.lean
./lean/InfoGeometry/External/Auto/BostConnesDeformation.lean
./lean/InfoGeometry/External/Auto/BPSPositiveEnergyBound.lean
./lean/InfoGeometry/External/Auto/BraidedCocycleWilsonEntropy.lean
./lean/InfoGeometry/External/Auto/BraidGroup.lean
./lean/InfoGeometry/External/Auto/BraidInductiveColimitCategory.lean
./lean/InfoGeometry/External/Auto/BraidInductiveColimitComplement.lean
./lean/InfoGeometry/External/Auto/BrillouinKleinNilpotentAttractor.lean
./lean/InfoGeometry/External/Auto/BuresInformationGeodesicFlow.lean
./lean/InfoGeometry/External/Auto/BuresMetricClosedCartography.lean
./lean/InfoGeometry/External/Auto/CakirliPnInteractionIsospin.lean
./lean/InfoGeometry/External/Auto/CanonicalSouriauPauliThermodynamics.lean
./lean/InfoGeometry/External/Auto/CapstoneCondensate.lean
./lean/InfoGeometry/External/Auto/CapstoneCondensateLimits.lean
./lean/InfoGeometry/External/Auto/CARCCRCantorFock.lean
./lean/InfoGeometry/External/Auto/CartanTriality.lean
./lean/InfoGeometry/External/Auto/CartanWeylBogoliubovGravity.lean
./lean/InfoGeometry/External/Auto/CasimirIsospinHamiltonian.lean
./lean/InfoGeometry/External/Auto/CauchyHolography.lean
./lean/InfoGeometry/External/Auto/CauchyHorizonBoseCondensate.lean
./lean/InfoGeometry/External/Auto/CausalityCondensate.lean
./lean/InfoGeometry/External/Auto/CausalPosetEntropy.lean
./lean/InfoGeometry/External/Auto/CausalStructure.lean
./lean/InfoGeometry/External/Auto/CayleyHilbertPolyaBraid.lean
./lean/InfoGeometry/External/Auto/CayleySchreierGauge.lean
./lean/InfoGeometry/External/Auto/CheckLimit.lean
./lean/InfoGeometry/External/Auto/CheckPUnitAdd.lean
./lean/InfoGeometry/External/Auto/ChemicalPotentialMetricBridge.lean
./lean/InfoGeometry/External/Auto/ChiralAffineBogoliubovWeld.lean
./lean/InfoGeometry/External/Auto/ChiralCuntzInductive.lean
./lean/InfoGeometry/External/Auto/ChiralTwistedFibration.lean
./lean/InfoGeometry/External/Auto/CKMAeonColimit.lean
./lean/InfoGeometry/External/Auto/CliffordInductiveTripotent.lean
./lean/InfoGeometry/External/Auto/clifford_seed.lean
./lean/InfoGeometry/External/Auto/CofactorExpansion.lean
./lean/InfoGeometry/External/Auto/CognitiveAccretionDiskSelfReferential.lean
./lean/InfoGeometry/External/Auto/CoherentOrbitalPrecession.lean
./lean/InfoGeometry/External/Auto/CompleteHolographicDictionary.lean
./lean/InfoGeometry/External/Auto/ComplexTemperatureRH.lean
./lean/InfoGeometry/External/Auto/ConformalModel.lean
./lean/InfoGeometry/External/Auto/ConnesMarcolliShimura.lean
./lean/InfoGeometry/External/Auto/ConnesSpectralAction.lean
./lean/InfoGeometry/External/Auto/ContinuumAsColimitCounting.lean
./lean/InfoGeometry/External/Auto/ConvexAlgebraicDuality.lean
./lean/InfoGeometry/External/Auto/CooperadEnvironmentalRank32.lean
./lean/InfoGeometry/External/Auto/CPTCausalCone.lean
./lean/InfoGeometry/External/Auto/CPTDeRhamCohomology.lean
./lean/InfoGeometry/External/Auto/CptFractalClosure.lean
./lean/InfoGeometry/External/Auto/CPTKreinTowerBridge.lean
./lean/InfoGeometry/External/Auto/CptTensorFractal.lean
./lean/InfoGeometry/External/Auto/CramerRaoFisher.lean
./lean/InfoGeometry/External/Auto/Crystallographic.lean
./lean/InfoGeometry/External/Auto/CubicJordanPeirceDecomposition.lean
./lean/InfoGeometry/External/Auto/CuntzAlgebra.lean
./lean/InfoGeometry/External/Auto/CuntzBraidCantor.lean
./lean/InfoGeometry/External/Auto/CuntzInverseLimit.lean
./lean/InfoGeometry/External/Auto/CuntzK0TorsionRelation.lean
./lean/InfoGeometry/External/Auto/CuntzKriegerFibonacciK.lean
./lean/InfoGeometry/External/Auto/CuntzKriegerKTheory.lean
./lean/InfoGeometry/External/Auto/CuntzKriegerPrimon.lean
./lean/InfoGeometry/External/Auto/CuntzKTheoryMittagLeffler.lean
./lean/InfoGeometry/External/Auto/CuntzKTheoryPairing.lean
./lean/InfoGeometry/External/Auto/CuntzZornEntropy.lean
./lean/InfoGeometry/External/Auto/CurveOrientation.lean
./lean/InfoGeometry/External/Auto/D4TrialityUniverse.lean
./lean/InfoGeometry/External/Auto/DeterminantSupergrading.lean
./lean/InfoGeometry/External/Auto/determinant_weyl_gauge.lean
./lean/InfoGeometry/External/Auto/DikinGoutevTonevBridge.lean
./lean/InfoGeometry/External/Auto/DiracFourierMellin.lean
./lean/InfoGeometry/External/Auto/DiracKreinMetriplectic.lean
./lean/InfoGeometry/External/Auto/DiracResolventZeroModeTripotent.lean
./lean/InfoGeometry/External/Auto/DiracZeroModes.lean
./lean/InfoGeometry/External/Auto/discrete_maxflow_mincut.lean
./lean/InfoGeometry/External/Auto/DupontHypersurfaceOSModel.lean
./lean/InfoGeometry/External/Auto/EfficientDeterminant.lean
./lean/InfoGeometry/External/Auto/EinsteinStimulatedBoseCollapse.lean
./lean/InfoGeometry/External/Auto/EinsteinThermodynamicBridge.lean
./lean/InfoGeometry/External/Auto/EinsteinTKK.lean
./lean/InfoGeometry/External/Auto/EmergentSpacetimeAnsatz.lean
./lean/InfoGeometry/External/Auto/EntropicHodgeDecomposition.lean
./lean/InfoGeometry/External/Auto/ExceptionalKleinGlideEP.lean
./lean/InfoGeometry/External/Auto/ExceptionalNonorientableTopology.lean
./lean/InfoGeometry/External/Auto/ExceptionalTopologicalBandStructures.lean
./lean/InfoGeometry/External/Auto/ExtractBraid.lean
./lean/InfoGeometry/External/Auto/FarneaGe64IsospinMixing.lean
./lean/InfoGeometry/External/Auto/FenchelSpacetime.lean
./lean/InfoGeometry/External/Auto/FermiLevelGap.lean
./lean/InfoGeometry/External/Auto/FermionicPrimonIndex.lean
./lean/InfoGeometry/External/Auto/FermionicPrimonPartition.lean
./lean/InfoGeometry/External/Auto/FibAnyonThm1.lean
./lean/InfoGeometry/External/Auto/FibAnyonThm2.lean
./lean/InfoGeometry/External/Auto/FibAnyonThm3.lean
./lean/InfoGeometry/External/Auto/FibAnyonThm4.lean
./lean/InfoGeometry/External/Auto/FibAnyonThm5.lean
./lean/InfoGeometry/External/Auto/FibAnyonThm6_pentagon.lean
./lean/InfoGeometry/External/Auto/FibAnyonThm7_hexagon.lean
./lean/InfoGeometry/External/Auto/FiniteArithmeticUHFTrace.lean
./lean/InfoGeometry/External/Auto/FiniteDirichletOccupation.lean
./lean/InfoGeometry/External/Auto/FiniteGNSConstruction.lean
./lean/InfoGeometry/External/Auto/FiniteMatrixElementDuality.lean
./lean/InfoGeometry/External/Auto/FiniteMobiusCoefficient.lean
./lean/InfoGeometry/External/Auto/FinitePrimeFock.lean
./lean/InfoGeometry/External/Auto/FiniteProjectorSpectralCalculus.lean
./lean/InfoGeometry/External/Auto/FiniteUHFBooleanTrace.lean
./lean/InfoGeometry/External/Auto/FixedLineRiemannKlein.lean
./lean/InfoGeometry/External/Auto/FockSpaceDerivation.lean
./lean/InfoGeometry/External/Auto/FockUHFBridge.lean
./lean/InfoGeometry/External/Auto/formal-theory.lean
./lean/InfoGeometry/External/Auto/FractalHamiltonian.lean
./lean/InfoGeometry/External/Auto/FractalKleinSUSYFramework.lean
./lean/InfoGeometry/External/Auto/FredholmModularRegularization.lean
./lean/InfoGeometry/External/Auto/FredholmRegularization.lean
./lean/InfoGeometry/External/Auto/FreedAnomalyCancellation.lean
./lean/InfoGeometry/External/Auto/FreedHeteroticTorsion.lean
./lean/InfoGeometry/External/Auto/FureyLadderSerreResidues.lean
./lean/InfoGeometry/External/Auto/FureyZornFermionBridge.lean
./lean/InfoGeometry/External/Auto/FusOctonionKKS.lean
./lean/InfoGeometry/External/Auto/GellMannCartan.lean
./lean/InfoGeometry/External/Auto/GeneralizedMirrorNuclei.lean
./lean/InfoGeometry/External/Auto/GeometricZeta.lean
./lean/InfoGeometry/External/Auto/GlideDiracSelectionRule.lean
./lean/InfoGeometry/External/Auto/GlideModularJ.lean
./lean/InfoGeometry/External/Auto/GlideSuperchargeCasimir.lean
./lean/InfoGeometry/External/Auto/GlideSymmetricInvariant.lean
./lean/InfoGeometry/External/Auto/GNSConstruction.lean
./lean/InfoGeometry/External/Auto/GNSModularObservables.lean
./lean/InfoGeometry/External/Auto/GNSQuotientFinite.lean
./lean/InfoGeometry/External/Auto/GohbergKreinIndex.lean
./lean/InfoGeometry/External/Auto/GoldenCCR.lean
./lean/InfoGeometry/External/Auto/GoldenSpectralTriple.lean
./lean/InfoGeometry/External/Auto/goutev_principle.lean
./lean/InfoGeometry/External/Auto/GoutevTonevPrinciple.lean
./lean/InfoGeometry/External/Auto/GrandCanonicalBerezinian.lean
./lean/InfoGeometry/External/Auto/GrandCanonicalPrimon.lean
./lean/InfoGeometry/External/Auto/GrandHolographicTheorem.lean
./lean/InfoGeometry/External/Auto/GrandUnifiedVacuum.lean
./lean/InfoGeometry/External/Auto/GravitySoldering.lean
./lean/InfoGeometry/External/Auto/GT_FromText.lean
./lean/InfoGeometry/External/Auto/GuptaAdaptVQERandomHamiltonians.lean
./lean/InfoGeometry/External/Auto/HeavyIsospinMixingSystematics.lean
./lean/InfoGeometry/External/Auto/HestenesKreinColimitBridge.lean
./lean/InfoGeometry/External/Auto/HexagonCocycle.lean
./lean/InfoGeometry/External/Auto/HolographicArchitect.lean
./lean/InfoGeometry/External/Auto/HolographicErlangenCompletion.lean
./lean/InfoGeometry/External/Auto/HolographicMonodromy.lean
./lean/InfoGeometry/External/Auto/HolographicScaleExtinctions.lean
./lean/InfoGeometry/External/Auto/HoTTInfinityBridge.lean
./lean/InfoGeometry/External/Auto/ImprovedLLMTheory.lean
./lean/InfoGeometry/External/Auto/inductive_colimit_uhf_group.lean
./lean/InfoGeometry/External/Auto/InfinityAnomalyWiring.lean
./lean/InfoGeometry/External/Auto/InfinityFilteredColimits.lean
./lean/InfoGeometry/External/Auto/InformationGeometricCutoff.lean
./lean/InfoGeometry/External/Auto/InstantonQCD.lean
./lean/InfoGeometry/External/Auto/iR.lean
./lean/InfoGeometry/External/Auto/IsospinSymmetryBreaking.lean
./lean/InfoGeometry/External/Auto/ItakuraSaitoThermodynamics.lean
./lean/InfoGeometry/External/Auto/JaynesFinitePartitionColimit.lean
./lean/InfoGeometry/External/Auto/JaynesFiniteSetsColimitBridge.lean
./lean/InfoGeometry/External/Auto/JaynesLDDPGNSColimit.lean
./lean/InfoGeometry/External/Auto/JaynesLeanColimitBridge.lean
./lean/InfoGeometry/External/Auto/J_duality_chain.lean
./lean/InfoGeometry/External/Auto/JordanBlock2.lean
./lean/InfoGeometry/External/Auto/JordanLieMetriplectic.lean
./lean/InfoGeometry/External/Auto/KanekoA67HighSpinMED.lean
./lean/InfoGeometry/External/Auto/KaneMeleOrbifold.lean
./lean/InfoGeometry/External/Auto/KANFourierMellinDirac.lean
./lean/InfoGeometry/External/Auto/KasparovKreinDoubling.lean
./lean/InfoGeometry/External/Auto/KleinBottleCobordism.lean
./lean/InfoGeometry/External/Auto/KleinBottle.lean
./lean/InfoGeometry/External/Auto/KleinGeometrySupergraded.lean
./lean/InfoGeometry/External/Auto/KleinGrapheneTunneling.lean
./lean/InfoGeometry/External/Auto/KoroteevZeitlin3DMirror.lean
./lean/InfoGeometry/External/Auto/KreinMoorePenrose.lean
./lean/InfoGeometry/External/Auto/krein_souriau_full.lean
./lean/InfoGeometry/External/Auto/krein_souriau.lean
./lean/InfoGeometry/External/Auto/LanglandsGromovWitten.lean
./lean/InfoGeometry/External/Auto/LECM2022ElectroweakRadiiISB.lean
./lean/InfoGeometry/External/Auto/LegendreFenchelSpectralGap.lean
./lean/InfoGeometry/External/Auto/LicataFinsterEMSpaces.lean
./lean/InfoGeometry/External/Auto/LightConeTripotentMatrixBridge.lean
./lean/InfoGeometry/External/Auto/LiuCollinsAffineInvariance.lean
./lean/InfoGeometry/External/Auto/LlewellynZr79MED.lean
./lean/InfoGeometry/External/Auto/LocalConcavity.lean
./lean/InfoGeometry/External/Auto/LogDeterminantHomomorphism.lean
./lean/InfoGeometry/External/Auto/LogDetSuperKahlerBarrier.lean
./lean/InfoGeometry/External/Auto/LQGProblemsResolvedByChiralFramework.lean
./lean/InfoGeometry/External/Auto/MajoranaPrimonSpectralBridge.lean
./lean/InfoGeometry/External/Auto/master_equation.lean
./lean/InfoGeometry/External/Automath/SpectralSquashCayleyDKT.lean
./lean/InfoGeometry/External/Auto/MaxCalFeynmanGaussBonnet.lean
./lean/InfoGeometry/External/Auto/MellinWaveletScaleShiftDigest.lean
./lean/InfoGeometry/External/Auto/MetriplecticCausality.lean
./lean/InfoGeometry/External/Auto/MinkowskiBiquaternion.lean
./lean/InfoGeometry/External/Auto/MITFInvariant.lean
./lean/InfoGeometry/External/Auto/MITFOrientabilityFlow.lean
./lean/InfoGeometry/External/Auto/MITFOrientability.lean
./lean/InfoGeometry/External/Auto/MobiusInversion.lean
./lean/InfoGeometry/External/Auto/MobiusWittenIndex.lean
./lean/InfoGeometry/External/Auto/MobiusWittenKleinIndex.lean
./lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean
./lean/InfoGeometry/External/Auto/ModularAutomorphismGroup.lean
./lean/InfoGeometry/External/Auto/ModularGlideCPT.lean
./lean/InfoGeometry/External/Auto/ModularHolographicMetric.lean
./lean/InfoGeometry/External/Auto/ModularItakuraBiquaternion.lean
./lean/InfoGeometry/External/Auto/ModularKreinReflectionColimit.lean
./lean/InfoGeometry/External/Auto/ModularMonodromy.lean
./lean/InfoGeometry/External/Auto/ModuleCatCohomology.lean
./lean/InfoGeometry/External/Auto/MorandiWallpaperCohomology.lean
./lean/InfoGeometry/External/Auto/NoncommutativeTilingAlgebra.lean
./lean/InfoGeometry/External/Auto/NonInvertiblePenroseCategoricalSymmetry.lean
./lean/InfoGeometry/External/Auto/NonIsoConf3DeRhamCohomologyFormula.lean
./lean/InfoGeometry/External/Auto/NonIsoConf3DeRhamCooperad.lean
./lean/InfoGeometry/External/Auto/NonIsoConf3DupontGysinModel.lean
./lean/InfoGeometry/External/Auto/NonIsoConf3LogCFTPotential.lean
./lean/InfoGeometry/External/Auto/NonIsoConf3LogWedgeObstruction.lean
./lean/InfoGeometry/External/Auto/NonIsoConf3OrlikSolomon.lean
./lean/InfoGeometry/External/Auto/NonIsoConf3QuadricCompactification.lean
./lean/InfoGeometry/External/Auto/NonIsoConf3QuadricD4Model.lean
./lean/InfoGeometry/External/Auto/NonIsoConf3QuadricD4PointCount.lean
./lean/InfoGeometry/External/Auto/NonIsoConf3RankDecision.lean
./lean/InfoGeometry/External/Auto/NonOrientableBraid.lean
./lean/InfoGeometry/External/Auto/NuclearChartSquareCalibration.lean
./lean/InfoGeometry/External/Auto/NuclearPhononGenerators.lean
./lean/InfoGeometry/External/Auto/NuclearPhononMetriplecticBridge.lean
./lean/InfoGeometry/External/Auto/NumberSystemColimits.lean
./lean/InfoGeometry/External/Auto/OakuTakayamaDModuleDeRham.lean
./lean/InfoGeometry/External/Auto/OctonionMatrixEncodings.lean
./lean/InfoGeometry/External/Auto/Orientability.lean
./lean/InfoGeometry/External/Auto/OrlandiA67Proceedings.lean
./lean/InfoGeometry/External/Auto/PaperwallDiscreteSUSY.lean
./lean/InfoGeometry/External/Auto/PaperwallHolographicSUSY.lean
./lean/InfoGeometry/External/Auto/PaperwallSUSY.lean
./lean/InfoGeometry/External/Auto/PartitionPoleCriterion.lean
./lean/InfoGeometry/External/Auto/PauliZornTrifactor.lean
./lean/InfoGeometry/External/Auto/PenroseAF.lean
./lean/InfoGeometry/External/Auto/PenroseArithmetic.lean
./lean/InfoGeometry/External/Auto/PenroseCuntzKriegerHolography.lean
./lean/InfoGeometry/External/Auto/PenroseKMSSpectralDimension.lean
./lean/InfoGeometry/External/Auto/PenroseSpinIncidenceTessellation.lean
./lean/InfoGeometry/External/Auto/PenroseSpinNetworkChiralIsomorphism.lean
./lean/InfoGeometry/External/Auto/penrose_wallpaper_colimit.lean
./lean/InfoGeometry/External/Auto/PentagonPenroseWallpaperFractal.lean
./lean/InfoGeometry/External/Auto/PfaffianLineBundle.lean
./lean/InfoGeometry/External/Auto/PhaseTransition_SUSY.lean
./lean/InfoGeometry/External/Auto/Pin55AnomalyInflow.lean
./lean/InfoGeometry/External/Auto/PoissonGaussianGNSColimit.lean
./lean/InfoGeometry/External/Auto/PolynomialSymmetryOperators.lean
./lean/InfoGeometry/External/Auto/PrimaMateriaInformationGeometry.lean
./lean/InfoGeometry/External/Auto/PrimeMellinSymplecticCAR.lean
./lean/InfoGeometry/External/Auto/PrimonBosonFermionDuality.lean
./lean/InfoGeometry/External/Auto/PrimonFockTraceBridge.lean
./lean/InfoGeometry/External/Auto/PrimonHilbertPolyaSeparation.lean
./lean/InfoGeometry/External/Auto/PrimonSuperThermodynamics.lean
./lean/InfoGeometry/External/Auto/primon_system.lean
./lean/InfoGeometry/External/Auto/PrimonZetaMobius.lean
./lean/InfoGeometry/External/Auto/PRL124RuPairingSymmetry.lean
./lean/InfoGeometry/External/Auto/ProjectiveCrystalKappa.lean
./lean/InfoGeometry/External/Auto/ProjectiveCrystalMackeyDecomposition.lean
./lean/InfoGeometry/External/Auto/ProjectiveCrystalSymmetry.lean
./lean/InfoGeometry/External/Auto/ProjectiveCrystalTopology.lean
./lean/InfoGeometry/External/Auto/ProjectiveCuntzToeplitzCARCCR.lean
./lean/InfoGeometry/External/Auto/ProjectiveGlideSuperchargeUnification.lean
./lean/InfoGeometry/External/Auto/ProjectiveKappaKleinMobius.lean
./lean/InfoGeometry/External/Auto/ProjectiveMobiusMatrix.lean
./lean/InfoGeometry/External/Auto/ProjectivePenrosePGA.lean
./lean/InfoGeometry/External/Auto/ProjectiveSymmetryAlgebra.lean
./lean/InfoGeometry/External/Auto/ProjectiveWallpaperGaugePSA.lean
./lean/InfoGeometry/External/Auto/PublishedThesisArchitecture.lean
./lean/InfoGeometry/External/Auto/Q8NuclearChirality.lean
./lean/InfoGeometry/External/Auto/QCDConfinementISDivergence.lean
./lean/InfoGeometry/External/Auto/QDeformedSuperCuntz.lean
./lean/InfoGeometry/External/Auto/QRootOfUnityTruncation.lean
./lean/InfoGeometry/External/Auto/QuadraticConfiguration3.lean
./lean/InfoGeometry/External/Auto/QuadricConf3BraidingCooperadBridge.lean
./lean/InfoGeometry/External/Auto/RamanScattering.lean
./lean/InfoGeometry/External/Auto/RaychaudhuriConformalBregman.lean
./lean/InfoGeometry/External/Auto/RegularizationCayleyPipeline.lean
./lean/InfoGeometry/External/Auto/RelativeModularStateDikin.lean
./lean/InfoGeometry/External/Auto/RelativisticBiquaternionKAN.lean
./lean/InfoGeometry/External/Auto/RescaledPhaseVolumeCanonical.lean
./lean/InfoGeometry/External/Auto/RGFixedPoint.lean
./lean/InfoGeometry/External/Auto/RiemannHypothesisIJIRT172568.lean
./lean/InfoGeometry/External/Auto/RiemannHypothesis.lean
./lean/InfoGeometry/External/Auto/RiemannKleinDuality.lean
./lean/InfoGeometry/External/Auto/rigorous_proofs.lean
./lean/InfoGeometry/External/Auto/RP3Octupole.lean
./lean/InfoGeometry/External/Auto/RunExtractor.lean
./lean/InfoGeometry/External/Auto/S3ColorSpinorDecomposition.lean
./lean/InfoGeometry/External/Auto/SarkarTwoLevelIsospinMixing.lean
./lean/InfoGeometry/External/Auto/SarsArangoBridge.lean
./lean/InfoGeometry/External/Auto/SarsBregmanDuality.lean
./lean/InfoGeometry/External/Auto/SarsCasimirSpring.lean
./lean/InfoGeometry/External/Auto/SarsChiralMassDilaton.lean
./lean/InfoGeometry/External/Auto/SarsGNSCompletion.lean
./lean/InfoGeometry/External/Auto/SarsGNSFronsdalJoseph.lean
./lean/InfoGeometry/External/Auto/SarsGNSWeyl.lean
./lean/InfoGeometry/External/Auto/SarsItakuraModular.lean
./lean/InfoGeometry/External/Auto/SarsMetriplecticOT.lean
./lean/InfoGeometry/External/Auto/SarsModularWeakValue.lean
./lean/InfoGeometry/External/Auto/SarsRoadblock.lean
./lean/InfoGeometry/External/Auto/SarsSKMajoranaSYK.lean
./lean/InfoGeometry/External/Auto/SarsSouriauDilaton.lean
./lean/InfoGeometry/External/Auto/SarsSU5Cl55Supertrace.lean
./lean/InfoGeometry/External/Auto/SarsWeylColimit.lean
./lean/InfoGeometry/External/Auto/ScratchSelfConcordant.lean
./lean/InfoGeometry/External/Auto/SelbergTraceFormula.lean
./lean/InfoGeometry/External/Auto/SerreSpectralSplitOctonion.lean
./lean/InfoGeometry/External/Auto/SheikhIsospinSymmetryBreaking.lean
./lean/InfoGeometry/External/Auto/SmithHatIsingDuality.lean
./lean/InfoGeometry/External/Auto/SO55NullSU5KleinSpectral.lean
./lean/InfoGeometry/External/Auto/SolderingForms.lean
./lean/InfoGeometry/External/Auto/SolderingRoundTrip.lean
./lean/InfoGeometry/External/Auto/SolovievQPNMChiralCuntz.lean
./lean/InfoGeometry/External/Auto/SouriauBiquaternionGaussian.lean
./lean/InfoGeometry/External/Auto/SouriauCasimirEntropyLeaves.lean
./lean/InfoGeometry/External/Auto/SouriauComplexTemperature.lean
./lean/InfoGeometry/External/Auto/SouriauGaussian.lean
./lean/InfoGeometry/External/Auto/SouriauHestenesKrein.lean
./lean/InfoGeometry/External/Auto/SouriauHestenesMobiusPole.lean
./lean/InfoGeometry/External/Auto/SouriauOperatorThermodynamics.lean
./lean/InfoGeometry/External/Auto/SouriauThermoColimit.lean
./lean/InfoGeometry/External/Auto/SpacetimeGUEIsomorphism.lean
./lean/InfoGeometry/External/Auto/SpacetimeIsSpin.lean
./lean/InfoGeometry/External/Auto/SpectralYangBaxter.lean
./lean/InfoGeometry/External/Auto/SpinorialVolumeFlow.lean
./lean/InfoGeometry/External/Auto/SpinorMonodromySteppingStone.lean
./lean/InfoGeometry/External/Auto/SpinorVectorDuality.lean
./lean/InfoGeometry/External/Auto/SplitOctonionMinkowski.lean
./lean/InfoGeometry/External/Auto/SplitOctonionNilpotent.lean
./lean/InfoGeometry/External/Auto/SplitOctonionZornKKS.lean
./lean/InfoGeometry/External/Auto/SquashingOperator.lean
./lean/InfoGeometry/External/Auto/StrongCPAeonTheta.lean
./lean/InfoGeometry/External/Auto/SU3LoopBraidDuality.lean
./lean/InfoGeometry/External/Auto/SullivanShimuraTransfer.lean
./lean/InfoGeometry/External/Auto/SUNLoopBraidCuntzBoundary.lean
./lean/InfoGeometry/External/Auto/SuperBerezinianKlein.lean
./lean/InfoGeometry/External/Auto/SuperchargeSquare.lean
./lean/InfoGeometry/External/Auto/SuperPartitionBerezinian.lean
./lean/InfoGeometry/External/Auto/SymbolicFockLane.lean
./lean/InfoGeometry/External/Auto/SymbolicLaneUHFBridge.lean
./lean/InfoGeometry/External/Auto/SymmetryReviewISB.lean
./lean/InfoGeometry/External/Auto/T5Z2AnomalyCancellation.lean
./lean/InfoGeometry/External/Auto/temp.lean
./lean/InfoGeometry/External/Auto/test3.lean
./lean/InfoGeometry/External/Auto/test4.lean
./lean/InfoGeometry/External/Auto/TestAF.lean
./lean/InfoGeometry/External/Auto/test_braid.lean
./lean/InfoGeometry/External/Auto/TestBraid.lean
./lean/InfoGeometry/External/Auto/TestFib.lean
./lean/InfoGeometry/External/Auto/TestImport2.lean
./lean/InfoGeometry/External/Auto/TestImportGP.lean
./lean/InfoGeometry/External/Auto/TestImportKB.lean
./lean/InfoGeometry/External/Auto/test_noncomm.lean
./lean/InfoGeometry/External/Auto/test_ring.lean
./lean/InfoGeometry/External/Auto/TestSelfAdjoint.lean
./lean/InfoGeometry/External/Auto/test_simp.lean
./lean/InfoGeometry/External/Auto/test_smul2.lean
./lean/InfoGeometry/External/Auto/test_smul.lean
./lean/InfoGeometry/External/Auto/TestTL.lean
./lean/InfoGeometry/External/Auto/test_wrapper.lean
./lean/InfoGeometry/External/Auto/thermo_gauge_flow.lean
./lean/InfoGeometry/External/Auto/ThesisMaster.lean
./lean/InfoGeometry/External/Auto/ThreeDMirrorSymmetry.lean
./lean/InfoGeometry/External/Auto/TKKCartanDecomposition.lean
./lean/InfoGeometry/External/Auto/TKKCompileData.lean
./lean/InfoGeometry/External/Auto/TKKQQBridge.lean
./lean/InfoGeometry/External/Auto/TKK_StandardModel.lean
./lean/InfoGeometry/External/Auto/tomita_kms_v4.lean
./lean/InfoGeometry/External/Auto/TomitaTakesakiRelativeEntropy.lean
./lean/InfoGeometry/External/Auto/TPUAQLattice.lean
./lean/InfoGeometry/External/Auto/TransformsAndScale.lean
./lean/InfoGeometry/External/Auto/TrifactorGeometry.lean
./lean/InfoGeometry/External/Auto/TripotentCliffordColimit.lean
./lean/InfoGeometry/External/Auto/TripotentPenroseHolography.lean
./lean/InfoGeometry/External/Auto/TwistedOrbifoldVacuum.lean
./lean/InfoGeometry/External/Auto/uhf_cantor_boundary.lean
./lean/InfoGeometry/External/Auto/UHFInductiveColimit.lean
./lean/InfoGeometry/External/Auto/uhf_ladder.lean
./lean/InfoGeometry/External/Auto/UnifiedKleinHolographicArchitecture.lean
./lean/InfoGeometry/External/Auto/UthayakumaarMirrorKnockout.lean
./lean/InfoGeometry/External/Auto/V4.lean
./lean/InfoGeometry/External/Auto/V4_test2.lean
./lean/InfoGeometry/External/Auto/VacuumCohomology.lean
./lean/InfoGeometry/External/Auto/VacuumGroundstate.lean
./lean/InfoGeometry/External/Auto/VacuumJonesKleinBirefringence.lean
./lean/InfoGeometry/External/Auto/VarlamovKleinSpectral.lean
./lean/InfoGeometry/External/Auto/VerberckWallpaperFourier.lean
./lean/InfoGeometry/External/Auto/VertexAlgebraBraidingCocycle.lean
./lean/InfoGeometry/External/Auto/VirasoroFinsupp.lean
./lean/InfoGeometry/External/Auto/WallpaperBulkAnyonProjection.lean
./lean/InfoGeometry/External/Auto/WallpaperClassification.lean
./lean/InfoGeometry/External/Auto/WallpaperCohomology.lean
./lean/InfoGeometry/External/Auto/WallpaperFermionSuperconductingGap.lean
./lean/InfoGeometry/External/Auto/WallpaperIsometry.lean
./lean/InfoGeometry/External/Auto/WallpaperMetamaterialDataset.lean
./lean/InfoGeometry/External/Auto/WallpaperSemidirectProduct.lean
./lean/InfoGeometry/External/Auto/WarehamCGADilatorSL2.lean
./lean/InfoGeometry/External/Auto/WarehamNullBasis55.lean
./lean/InfoGeometry/External/Auto/WeakIsospinSU2.lean
./lean/InfoGeometry/External/Auto/WeylGaugeItakuraSaito.lean
./lean/InfoGeometry/External/Auto/WignerMadelungKrein.lean
./lean/InfoGeometry/External/Auto/WittenIndex.lean
./lean/InfoGeometry/External/Auto/YanevaPd94PnSymmetry.lean
./lean/InfoGeometry/External/Auto/YangBaxterQuotientDescent.lean
./lean/InfoGeometry/External/Auto/ZetaInformationGeometry.lean
./lean/InfoGeometry/External/Auto/zeta_zeros_moebius_klein.lean
./lean/InfoGeometry/External/Auto/ZornAssociatorSplitOctonion.lean
./lean/InfoGeometry/External/Auto/ZornKleinGlideBridge.lean
./lean/InfoGeometry/External/Auto/ZornOPParavector.lean
./lean/InfoGeometry/External/Auto/ZornParavectorNullspace.lean
./lean/InfoGeometry/External/Auto/ZornScalingFlowOrdered.lean
./lean/InfoGeometry/External/Virasoro/AffineKacMoody.lean
./lean/InfoGeometry/External/Virasoro/CentralChargeCalc.lean
./lean/InfoGeometry/External/Virasoro/CentralExtension.lean
./lean/InfoGeometry/External/Virasoro/ChiralProduct.lean
./lean/InfoGeometry/External/Virasoro/Commutator.lean
./lean/InfoGeometry/External/Virasoro/CyclicTripleSum.lean
./lean/InfoGeometry/External/Virasoro/FiveGradedDecomposition.lean
./lean/InfoGeometry/External/Virasoro/FockSpace.lean
./lean/InfoGeometry/External/Virasoro/FockSpaceSugawara.lean
./lean/InfoGeometry/External/Virasoro/HeisenbergAlgebra.lean
./lean/InfoGeometry/External/Virasoro/HeisenbergFlip.lean
./lean/InfoGeometry/External/Virasoro/HeisenbergModeFlip.lean
./lean/InfoGeometry/External/Virasoro/IndexTri.lean
./lean/InfoGeometry/External/Virasoro/IsCentralExtension.lean
./lean/InfoGeometry/External/Virasoro.lean
./lean/InfoGeometry/External/Virasoro/LieAlgebraModuleUEA.lean
./lean/InfoGeometry/External/Virasoro/LieAlgebraRepresentationOfBasis.lean
./lean/InfoGeometry/External/Virasoro/LieCohomologySmallDegree.lean
./lean/InfoGeometry/External/Virasoro/LieVerma.lean
./lean/InfoGeometry/External/Virasoro/SectionSES.lean
./lean/InfoGeometry/External/Virasoro/Sugawara.lean
./lean/InfoGeometry/External/Virasoro/ToMathlib/Algebra/Lie/Abelian.lean
./lean/InfoGeometry/External/Virasoro/ToMathlib/Algebra/Lie/Basic.lean
./lean/InfoGeometry/External/Virasoro/ToMathlib/LinearAlgebra/Basis/Defs.lean
./lean/InfoGeometry/External/Virasoro/ToMathlib/LinearAlgebra/Basis/FinsumRepr.lean
./lean/InfoGeometry/External/Virasoro/ToMathlib/LinearAlgebra/Finsupp/Supported.lean
./lean/InfoGeometry/External/Virasoro/ToMathlib/Topology/Algebra/BigOperators/FinProd.lean
./lean/InfoGeometry/External/Virasoro/ToMathlib/Topology/Algebra/ConstMulAction.lean
./lean/InfoGeometry/External/Virasoro/ToMathlib/Topology/Algebra/InfiniteSum/Basic.lean
./lean/InfoGeometry/External/Virasoro/ToMathlib/Topology/Algebra/Module/LinearMap/Defs.lean
./lean/InfoGeometry/External/Virasoro/ToMathlib/Topology/Order.lean
./lean/InfoGeometry/External/Virasoro/VermaModule.lean
./lean/InfoGeometry/External/Virasoro/VirasoroAlgebra.lean
./lean/InfoGeometry/External/Virasoro/VirasoroCocycle.lean
./lean/InfoGeometry/External/Virasoro/VirasoroVerma.lean
./lean/InfoGeometry/External/Virasoro/WittAlgebraCohomology.lean
./lean/InfoGeometry/External/Virasoro/WittAlgebra.lean
./lean/InfoGeometry/Fibonacci/All.lean
./lean/InfoGeometry/FormalAgentLib/Layer1.lean
./lean/InfoGeometry/FormalTheory.lean
./lean/InfoGeometry/Foundations/All.lean
./lean/InfoGeometry/Foundations/AxiomaticDependencyGraph.lean
./lean/InfoGeometry/Generated.lean
./lean/InfoGeometry/Geometry.lean
./lean/InfoGeometry/GrandUnification/BiQuaternionKahlerThermoBridge.lean
./lean/InfoGeometry/GrandUnification/WeylCharacterCantorBridge.lean
./lean/InfoGeometry/GromovProbability.lean
./lean/InfoGeometry/GW/All.lean
./lean/InfoGeometry/Hardware/Benchmark.lean
./lean/InfoGeometry/Hestenes/SpacetimeAlgebra.lean
./lean/InfoGeometry/HilbertTensorProduct.lean
./lean/InfoGeometry/HilbertTensorProduct/Phase2_HS2Ell2.lean
./lean/InfoGeometry/HilbertTensorProduct/Phase5_SpectralTheorem.lean
./lean/InfoGeometry/Holography/All.lean
./lean/InfoGeometry/Holography/WittenMobiusBekensteinComplement.lean
./lean/InfoGeometry/Inference/PoissonSinkhornLyapunov.lean
./lean/InfoGeometry/Information/BergmanBregman.lean
./lean/InfoGeometry/Information/DeRhamScore.lean
./lean/InfoGeometry/Information/FisherMetricGeodesicDistanceBridge.lean
./lean/InfoGeometry/Information/RelativeOrientation.lean
./lean/InfoGeometry/Information/SouriauFisherMoebiusInformationGeometryBridge.lean
./lean/InfoGeometry/JordanDecomposition/CyclicNilpotent.lean
./lean/InfoGeometry/JordanDecomposition.lean
./lean/InfoGeometry/JordanDecomposition/Scratch.lean
./lean/InfoGeometry/Kaehler/FubiniStudyAsymptotics.lean
./lean/InfoGeometry/Kaehler/PoincareMetric.lean
./lean/InfoGeometry/Krein/HestenesJonesGWVolumeBridge.lean
./lean/InfoGeometry/Lie/All.lean
./lean/InfoGeometry/Lie/CanonicalZornG2CartanSouriauCoadjointBridge.lean
./lean/InfoGeometry/Lie/CanonicalZornRootSystem.lean
./lean/InfoGeometry/Lie/CartanKrein.lean
./lean/InfoGeometry/Lie/MathlibBackportAdjointAction.lean
./lean/InfoGeometry/Lie/MathlibBackportAEval.lean
./lean/InfoGeometry/Lie/MathlibBackportBasisLieEnd.lean
./lean/InfoGeometry/Lie/MathlibBackportCartanCriterionFoundations.lean
./lean/InfoGeometry/Lie/MathlibBackportCartanCriterionFull.lean
./lean/InfoGeometry/Lie/MathlibBackportFreeBaseChange.lean
./lean/InfoGeometry/Lie/MathlibBackportJordanChevalley.lean
./lean/InfoGeometry/Lie/SplitG2SL3Concrete.lean
./lean/InfoGeometry/Lie/SplitOctonionStandardDerivationBasis.lean
./lean/InfoGeometry/Measure/ProjectiveState.lean
./lean/InfoGeometry/MellinColimitTrifactor.lean
./lean/InfoGeometry/Meta/FormalLogos.lean
./lean/InfoGeometry/Meta/GromovErgostructureBridge.lean
./lean/InfoGeometry/Meta.lean
./lean/InfoGeometry/Meta/ShadowLedger.lean
./lean/InfoGeometry/Meta/ThermodynamicGEORegulation.lean
./lean/InfoGeometry/Meta/TranscendentFunction.lean
./lean/InfoGeometry/Modular/ChoiCompletePositivity.lean
./lean/InfoGeometry/Modular/Classification.lean
./lean/InfoGeometry/Modular.lean
./lean/InfoGeometry/Monster/MonsterMoonshineThermal.lean
./lean/InfoGeometry/Network/All.lean
./lean/InfoGeometry/OperatorAlgebra/AndreevHorizonBridge.lean
./lean/InfoGeometry/OperatorAlgebra/ChiralCliffordSplit.lean
./lean/InfoGeometry/OperatorAlgebra/ChiralRetainedWordFiveGradeDecomposition.lean
./lean/InfoGeometry/OperatorAlgebra/ChiralTripotentSuperTKKLedger.lean
./lean/InfoGeometry/OperatorAlgebra/ConcreteWeylAnomaly.lean
./lean/InfoGeometry/OperatorAlgebra/D4StarCrossedProductAlgebraicSurface.lean
./lean/InfoGeometry/OperatorAlgebra/DoubledHestenesKreinMirror.lean
./lean/InfoGeometry/OperatorAlgebra/OperatorialJonesCalculus.lean
./lean/InfoGeometry/OperatorAlgebra/QCCRCarBridge.lean
./lean/InfoGeometry/OperatorAlgebra/QCCRZeroCuntzBridge.lean
./lean/InfoGeometry/OperatorAlgebra/RealONNOperatorLift.lean
./lean/InfoGeometry/OperatorAlgebra/SL2RModularFlow.lean
./lean/InfoGeometry/OperatorAlgebra/SpectralGeneratorProxy.lean
./lean/InfoGeometry/OperatorAlgebra/SplitOctonionGroundedCrossSection.lean
./lean/InfoGeometry/OperatorAlgebra/SusceptibilityHessian.lean
./lean/InfoGeometry/OperatorAlgebra/TripotentFactorization.lean
./lean/InfoGeometry/OperatorAlgebra/VirasoroProjectPin.lean
./lean/InfoGeometry/Optics/JonesCalculus.lean
./lean/InfoGeometry/Optics/JonesCalculusSpinorLorentz.lean
./lean/InfoGeometry/Peirce/PeirceLadderOperators.lean
./lean/InfoGeometry/Physics/AlgebraicCuntzQuotient.lean
./lean/InfoGeometry/Physics/Algebra/SuperWiesbrockKreinBridge.lean
./lean/InfoGeometry/Physics/AmplituhedronPenroseTransform.lean
./lean/InfoGeometry/Physics/BoundaryMajoranaDefectBridge.lean
./lean/InfoGeometry/Physics/ChiralityPseudoscalarCuntz.lean
./lean/InfoGeometry/Physics/ChiralTensorRecoupling.lean
./lean/InfoGeometry/Physics/ChiralUncertaintyCaliber.lean
./lean/InfoGeometry/Physics/Cl55FiniteShadowPacket.lean
./lean/InfoGeometry/Physics/ConcreteKleinBridge.lean
./lean/InfoGeometry/Physics/D4Triality_audit.lean
./lean/InfoGeometry/Physics/GogberashviliNilpotentCARBridge.lean
./lean/InfoGeometry/Physics/ItakuraSaitoInvariance.lean
./lean/InfoGeometry/Physics/KantorovichPairingHausdorffScaling.lean
./lean/InfoGeometry/Physics/MatrixTraceBimodulePairing.lean
./lean/InfoGeometry/Physics/MD015QuantumCorrectionsFinite.lean
./lean/InfoGeometry/Physics/MD017ConclusionFiniteLedger.lean
./lean/InfoGeometry/Physics/MDPASJMSouriauPaperDigest.lean
./lean/InfoGeometry/Physics/ParafermionicBECHiggs.lean
./lean/InfoGeometry/Physics/PellisFineStructure.lean
./lean/InfoGeometry/Physics/Section29QuantumEffectiveAction.lean
./lean/InfoGeometry/Physics/SinkhornEntropyPoissonDeviance.lean
./lean/InfoGeometry/Physics/SplitCliffordAlgebras.lean
./lean/InfoGeometry/Physics/TopologicalMTheoryGromovWitten.lean
./lean/InfoGeometry/Physics/WeylSU3ColorSymmetry.lean
./lean/InfoGeometry/Physics/ZornMatrixSU3.lean
./lean/InfoGeometry/Probability/GromovConcentration.lean
./lean/InfoGeometry/Probability/GromovFiniteCounting.lean
./lean/InfoGeometry/Probability/GromovJaynesProbability.lean
./lean/InfoGeometry/Probability/GromovPascalConcentration.lean
./lean/InfoGeometry/Probability/GromovProbability.lean
./lean/InfoGeometry/Probability/GromovProjectiveRatio.lean
./lean/InfoGeometry/Probability/GromovSystem.lean
./lean/InfoGeometry/Probability/SymmetricCounting.lean
./lean/InfoGeometry/Projective/BostConnesZetaComparison.lean
./lean/InfoGeometry/Projective/Compatibility.lean
./lean/InfoGeometry/Projective/QuantumTwistorDirac.lean
./lean/InfoGeometry/Projective/SplitOctonions/PolarConcrete.lean
./lean/InfoGeometry/Projective/SplitOctonions/ProjectiveZornPolarIncidence.lean
./lean/InfoGeometry/Projective/Twistor/Basic/Density.lean
./lean/InfoGeometry/Projective/Twistor/Basic.lean
./lean/InfoGeometry/Projective/Twistor/Basic/ParameterDomain.lean
./lean/InfoGeometry/Projective/Twistor/Basic/Reparametrization.lean
./lean/InfoGeometry/Projective/Twistor/Basic/StatisticalFamily.lean
./lean/InfoGeometry/Projective/TwistorSpace.lean
./lean/InfoGeometry/ProofTelemetry/Smoke.lean
./lean/InfoGeometry/Quantum/FibonacciFusionCategory.lean
./lean/InfoGeometry/Quantum/GeneralizedPauli.lean
./lean/InfoGeometry/QuantumGeometry/CompleteUnifiedBundle.lean
./lean/InfoGeometry/QuantumGeometry.lean
./lean/InfoGeometry/QuantumGeometry/Projective.lean
./lean/InfoGeometry/QuantumGeometry/ProjectiveNormalizedQGT.lean
./lean/InfoGeometry/QuantumGeometry/ProjectiveQuotientQGT.lean
./lean/InfoGeometry/Quiver/BetheAnsatzXXZ.lean
./lean/InfoGeometry/Quiver/HbarOper.lean
./lean/InfoGeometry/Quiver/KoroteevZeitlinMirror.lean
./lean/InfoGeometry/Quiver/TKKHamiltonian.lean
./lean/InfoGeometry/Quiver/XXZYangYang.lean
./lean/InfoGeometry/RedlineDictionary.lean
./lean/InfoGeometry/Routing/BirkhoffVonNeumann.lean
./lean/InfoGeometry/Sandbox/CliffordFunctorSandbox/Functor.lean
./lean/InfoGeometry/Sandbox/CliffordFunctorSandbox.lean
./lean/InfoGeometry/Sandbox/CliffordFunctorSandbox/Tower.lean
./lean/InfoGeometry/Sandbox/CliffordQuotientSandbox.lean
./lean/InfoGeometry/Sandbox/InfiniteColimitRigor.lean
./lean/InfoGeometry/Sandbox/KTheoryIndexSandbox.lean
./lean/InfoGeometry/Sandbox/LefschetzFixedPoint.lean
./lean/InfoGeometry/Sandbox/scratch_colim_test.lean
./lean/InfoGeometry/Sandbox/SpectralStabilitySandbox.lean
./lean/InfoGeometry/Section10_11.lean
./lean/InfoGeometry/Section10.lean
./lean/InfoGeometry/Section11.lean
./lean/InfoGeometry/Section12Formalized.lean
./lean/InfoGeometry/Section12.lean
./lean/InfoGeometry/Section13.lean
./lean/InfoGeometry/Section15.lean
./lean/InfoGeometry/Section16.lean
./lean/InfoGeometry/Section17.lean
./lean/InfoGeometry/Section18.lean
./lean/InfoGeometry/Section19.lean
./lean/InfoGeometry/Section20.lean
./lean/InfoGeometry/Section21.lean
./lean/InfoGeometry/Section22.lean
./lean/InfoGeometry/Section24.lean
./lean/InfoGeometry/Section25.lean
./lean/InfoGeometry/Section26.lean
./lean/InfoGeometry/Section2.lean
./lean/InfoGeometry/Section3.lean
./lean/InfoGeometry/Section4.lean
./lean/InfoGeometry/Section5.lean
./lean/InfoGeometry/Section6.lean
./lean/InfoGeometry/Section7.lean
./lean/InfoGeometry/Section8.lean
./lean/InfoGeometry/Section9.lean
./lean/InfoGeometry/SelfReference/ShadowCone.lean
./lean/InfoGeometry/Signal/All.lean
./lean/InfoGeometry/Singular/DrazinAdjoint.lean
./lean/InfoGeometry/Singular/MoorePenroseAdjoint.lean
./lean/InfoGeometry/Singular/MoorePenrose/ClosedRange.lean
./lean/InfoGeometry/Spectral/All.lean
./lean/InfoGeometry/Spectral/Cohomology/Gysin.lean
./lean/InfoGeometry/Spectral/Cohomology/ProjectiveSpace.lean
./lean/InfoGeometry/Spectral/Cohomology/Sandbox.lean
./lean/InfoGeometry/Spectral/Cohomology/SerreExactCouple.lean
./lean/InfoGeometry/Spectral/Colimit/SeqColim.lean
./lean/InfoGeometry/Spectral/RealProjective.lean
./lean/InfoGeometry/SuperMetriplectic/BlackHoleEntropy.lean
./lean/InfoGeometry/SuperMetriplectic/CasimirKLDissipationBridge.lean
./lean/InfoGeometry/SuperMetriplectic/CasimirZeta.lean
./lean/InfoGeometry/SuperMetriplectic/CriticalStiffness.lean
./lean/InfoGeometry/SuperMetriplectic/DarkEnergyMapping.lean
./lean/InfoGeometry/SuperMetriplectic/InformationEquilibrium.lean
./lean/InfoGeometry/SuperMetriplectic/InformationSuperGas.lean
./lean/InfoGeometry/SuperMetriplectic/MetriplecticSpectralDefectBridge.lean
./lean/InfoGeometry/SuperMetriplectic/OnsagerCasimirMoebiusBridge.lean
./lean/InfoGeometry/SuperMetriplectic/OnsagerCasimirMoebiusMetricBridge.lean
./lean/InfoGeometry/SuperMetriplectic/OperatorKLBKM.lean
./lean/InfoGeometry/SuperMetriplectic/SeeleyDeWitt.lean
./lean/InfoGeometry/SuperMetriplectic/SouriauTomitaBKM.lean
./lean/InfoGeometry/SuperMetriplectic/SupervolumeFunctional.lean
./lean/InfoGeometry/SuperMetriplectic/VonMangoldtMoebiusMetriplecticBridge.lean
./lean/InfoGeometry/Synthesis/DualExponentialArchitecture.lean
./lean/InfoGeometry/Tessellation/All.lean
./lean/InfoGeometry/Tessellation/CantorDiracSeaOperatorGeometry.lean
./lean/InfoGeometry/Thermo/SandboxComplexThermodynamicLiftTest.lean
./lean/InfoGeometry/Thermo/SandboxJacobianBregmanBridgeTest.lean
./lean/InfoGeometry/TKK/TKKTest.lean
./lean/InfoGeometry/Tooling/CertificateBridge.lean
./lean/InfoGeometry/Topological/All.lean
./lean/InfoGeometry/Topology/All.lean
./lean/InfoGeometry/Topology/AnyonBraidRepresentation.lean
./lean/InfoGeometry/Topology/BostConnesZetaVolume.lean
./lean/InfoGeometry/Topology/BregmanDivergence.lean
./lean/InfoGeometry/Topology/BrillouinKleinAgentVerification.lean
./lean/InfoGeometry/Topology/D4SingularityDBrane.lean
./lean/InfoGeometry/Topology/DBraneMatrixFactorization.lean
./lean/InfoGeometry/Topology/DelaunayAdjacentStructures.lean
./lean/InfoGeometry/Topology/GeneralizedCircleMobius.lean
./lean/InfoGeometry/Topology/PainleveIsomonodromy.lean
./lean/InfoGeometry/Topology/PrimaryFields.lean
./lean/InfoGeometry/Topology/SandboxMobiusSouriauThermodynamicFlowTest.lean
./lean/InfoGeometry/Topology/SandboxThermodynamicSL2MobiusFlowTest.lean
./lean/InfoGeometry/Topology/StoneCantorMathlib.lean
./lean/InfoGeometry/Topology/test_linarith.lean
./lean/InfoGeometry/Topology/ZetaSouriauMetriplecticCoherenceBridge.lean
./lean/InfoGeometry/TrifactorDecomposition.lean
./lean/InfoGeometry/TrifactorGeometry.lean
./lean/InfoGeometry/TrifactorProjectors.lean
./lean/InfoGeometry/Twistor/All.lean
./lean/InfoGeometry/TwistorSmoothness.lean
./lean/InfoGeometry/UnifiedMatrixBasis.lean
./lean/InfoGeometry/Volume/LogarithmicOrderParameterConnesBridge.lean
./lean/InfoGeometry/Wavelet/All.lean

=== Files declaring a non-InfoGeometry namespace (heuristic) ===
./lean/InfoGeometry/Algebra/BerezinianPfaffianBott.lean :: 24:namespace Audit.BerezinianPfaffianBott
./lean/InfoGeometry/Algebra/Cl11Fermions.lean :: 10:namespace Cl11Fermions
./lean/InfoGeometry/Algebra/CuntzFibonacciBraidInclusion.lean :: 13:namespace CuntzFibonacciBraidInclusion
./lean/InfoGeometry/Algebra/Det2.lean :: 4:namespace Audit
./lean/InfoGeometry/Algebra/FibonacciGradedOffDiagonalBridge.lean :: 12:namespace FibonacciParafermion
./lean/InfoGeometry/Algebra/FibonacciParafermion.lean :: 25:namespace FibonacciParafermion
./lean/InfoGeometry/Algebra/HodgeDiracDelta.lean :: 22:namespace Audit.HodgeDiracDelta
./lean/InfoGeometry/Algebra/Hypothesis1.lean :: 16:namespace Hypothesis1
./lean/InfoGeometry/Algebra/K0FibonacciRing.lean :: 16:namespace Audit.K0FibonacciRing
./lean/InfoGeometry/Algebra/KreinPosNegDecomposition.lean :: 20:namespace Audit.KreinPosNegDecomposition
./lean/InfoGeometry/Algebra/SplitCliffordTransformKernel.lean :: 16:namespace SplitCliffordTransformKernel
./lean/InfoGeometry/Algebra/SuperTraceBerezinian.lean :: 5:namespace Audit.SuperTraceBerezinian
./lean/InfoGeometry/Algebra/TriFacetMatrixRealization.lean :: 6:namespace Audit.TriFacetMatrixRealization
./lean/InfoGeometry/Algebra/TriFacetSpectralPowers.lean :: 3:namespace Audit
./lean/InfoGeometry/Algebra/TripotentClSUSYBridge.lean :: 34:namespace TripotentClSUSYBridge
./lean/InfoGeometry/Algebra/TripotentPeirceProjectorBridge.lean :: 11:namespace TripotentClSUSYBridge
./lean/InfoGeometry/Algebra/UnitizationNonAssoc.lean :: 9:namespace Unitization
./lean/InfoGeometry/Algebra/VerlindeSMatrix.lean :: 26:namespace Audit.VerlindeSMatrix
./lean/InfoGeometry/Algebra/ZornBdGDerivationBridge.lean :: 27:namespace PauliSolderedCrossProductBridge
./lean/InfoGeometry/Attention/LogSumExpAttention.lean :: 22:namespace AttentionIsQuantumFluid
./lean/InfoGeometry/Automath/Generated/auto_20260721_230011_1.lean :: 3:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/auto_20260721_230011_2.lean :: 3:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/causal_zorn_presheaf.lean :: 12:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/cuntz_fibonacci_resolvent.lean :: 3:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/cuntz_shift_commutativity.lean :: 3:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/cuntz_yang_baxter.lean :: 3:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/entropy_hessian_eq_fisher_inverse.lean :: 3:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/hyp_1_spectral_rigidity.lean :: 3:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/hyp_2_fibonacci_functional_calculus.lean :: 3:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/hyp_3_operator_roots.lean :: 3:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/hyp_4_braid_image.lean :: 3:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/hyp_5_k_theory.lean :: 3:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/hyp_pin55_krein.lean :: 4:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/omega_auto_omega_bost_connes_kms.lean :: 3:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/omega_auto_omega_circle_dimension.lean :: 4:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/omega_auto_omega_cuntz_shift.lean :: 3:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/omega_auto_omega_golden_ratio_seed.lean :: 4:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/omega_auto_omega_walsh_stokes.lean :: 4:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/omega_auto_omega_xi_zeta_interface.lean :: 3:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/omega_fib_complete.lean :: 5:namespace Omega.Generated
./lean/InfoGeometry/Automath/Generated/omega_fib_gcd.lean :: 3:namespace Omega.Generated
./lean/InfoGeometry/Automath/Generated/omega_fib_succ_pos.lean :: 4:namespace Omega.Generated
./lean/InfoGeometry/Automath/Generated/omega_fib_succ_succ.lean :: 4:namespace Omega.Generated
./lean/InfoGeometry/Automath/Generated/onsager_entropy_production_zero.lean :: 3:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/su3_gellmann_lie_algebra.lean :: 12:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/test_hyp.lean :: 7:namespace Automath.Generated
./lean/InfoGeometry/BostConnes/BostConnesThermofield.lean :: 18:namespace BostConnesThermofield
./lean/InfoGeometry/BottPeriodicityReconciliation.lean :: 60:namespace BottPeriodicityReconciliation
./lean/InfoGeometry/Canonical/AdSCFTEntanglementWedgeBridge.lean :: 16:namespace AdSCFT
./lean/InfoGeometry/Canonical/AInfinityAlgebraHigherAssociativity.lean :: 16:namespace AInfinityAlgebra
./lean/InfoGeometry/Canonical/AlgebraicStarEnvelopeNorm.lean :: 16:namespace CStarStateColimit.Native
./lean/InfoGeometry/Canonical/AlgebraicStarEnvelopeTopologicalRealization.lean :: 30:namespace CStarStateColimit.Native.FaithfulStarRepresentation
./lean/InfoGeometry/Canonical/AndreevReflectionKreinHorizonBridge.lean :: 18:namespace AndreevReflectionKreinHorizonBridge
./lean/InfoGeometry/Canonical/AnosovQuantumErgodicFlowBridge.lean :: 16:namespace AnosovQuantum
./lean/InfoGeometry/Canonical/AnyonCondensationDomainWallBridge.lean :: 17:namespace AnyonCondensationDomainWallBridge
./lean/InfoGeometry/Canonical/AnyonicStabilizerCodeDistance.lean :: 17:namespace AnyonicStabilizer
./lean/InfoGeometry/Canonical/AnyonYangBaxterBraiding.lean :: 17:namespace AnyonYangBaxter
./lean/InfoGeometry/Canonical/AreaLawEntropyViolationBridge.lean :: 14:namespace AreaLawViolation
./lean/InfoGeometry/Canonical/AtiyahSingerChiralIndex.lean :: 17:namespace AtiyahSingerIndex
./lean/InfoGeometry/Canonical/AtiyahTQFTCobordismBridge.lean :: 12:namespace AtiyahTQFT
./lean/InfoGeometry/Canonical/AubertPlymen.lean :: 32:namespace AubertPlymen
./lean/InfoGeometry/Canonical/BiquaternionKANnilpotent.lean :: 12:namespace BiquaternionKANnilpotent
./lean/InfoGeometry/Canonical/BiquaternionLaplaceTripotent.lean :: 13:namespace BiquaternionLaplaceTripotent
./lean/InfoGeometry/Canonical/BiquaternionLorentzPolarBridge.lean :: 10:namespace SplitOctonion
./lean/InfoGeometry/Canonical/BiquaternionNegativeRootsLog.lean :: 16:namespace BiquaternionNegativeRootsLog
./lean/InfoGeometry/Canonical/BisognanoWichmannUnruhAQFT.lean :: 17:namespace BisognanoWichmannUnruh
./lean/InfoGeometry/Canonical/BMSSymmetrySoftHairBridge.lean :: 16:namespace BMSSymmetry
./lean/InfoGeometry/Canonical/BostConnesKTheoryIntegration.lean :: 12:namespace BostConnesKTheoryIntegration
./lean/InfoGeometry/Canonical/CalabiYauMirrorSymmetryBridge.lean :: 16:namespace CalabiYauMirror
./lean/InfoGeometry/Canonical/CanonicalZornCliffordIsomorphism.lean :: 22:namespace CanonicalZornCliffordIsomorphism
./lean/InfoGeometry/Canonical/CanonicalZornCliffordRepresentation.lean :: 18:namespace CanonicalZornCliffordRepresentation
./lean/InfoGeometry/Canonical/CanonicalZornCompositionFiveGradeBridge.lean :: 26:namespace CanonicalZornCompositionFiveGradeBridge
./lean/InfoGeometry/Canonical/CanonicalZornCompositionTriality.lean :: 29:namespace CanonicalZornCompositionTriality
./lean/InfoGeometry/Canonical/CanonicalZornConformalProjectiveScalingAudit.lean :: 14:namespace ProjectiveAffineConformalClosure55
./lean/InfoGeometry/Canonical/CanonicalZornDiracConnectionRepresentation.lean :: 19:namespace CanonicalZornDiracConnectionRepresentation
./lean/InfoGeometry/Canonical/CanonicalZornFiveGradedClosure.lean :: 24:namespace CanonicalZornFiveGradedClosure
./lean/InfoGeometry/Canonical/CanonicalZornFiveGradeReversal.lean :: 15:namespace CanonicalZornFiveGradedClosure
./lean/InfoGeometry/Canonical/CanonicalZornFiveGradeSymmetryClosure.lean :: 19:namespace CanonicalZornFiveGradedClosure
./lean/InfoGeometry/Canonical/CanonicalZornIntegralSpinRepresentation.lean :: 14:namespace CanonicalZornIntegralSpinRepresentation
./lean/InfoGeometry/Canonical/CanonicalZornIntegralSpinSubgroup.lean :: 15:namespace CanonicalZornIntegralSpinSubgroup
./lean/InfoGeometry/Canonical/CanonicalZornIntegralSpinTrialityClosure.lean :: 20:namespace CanonicalZornIntegralSpinTrialityClosure
./lean/InfoGeometry/Canonical/CanonicalZornIntegralTrialityEquivariance.lean :: 16:namespace CanonicalZornIntegralTrialityEquivariance
./lean/InfoGeometry/Canonical/CanonicalZornNullCliffordClosure.lean :: 18:namespace CanonicalZornNullCliffordClosure
./lean/InfoGeometry/Canonical/CanonicalZornOuterTrialityGroup.lean :: 20:namespace CanonicalZornOuterTrialityGroup
./lean/InfoGeometry/Canonical/CanonicalZornProjectiveCore.lean :: 22:namespace CanonicalZornProjectiveTKKBridge
./lean/InfoGeometry/Canonical/CanonicalZornProjectiveTKKBridge.lean :: 23:namespace CanonicalZornProjectiveTKKBridge
./lean/InfoGeometry/Canonical/CanonicalZornRealComplexSpinBaseChange.lean :: 14:namespace CanonicalZornRealComplexSpinBaseChange
./lean/InfoGeometry/Canonical/CanonicalZornRealSpin44.lean :: 24:namespace CanonicalZornRealSpin44
./lean/InfoGeometry/Canonical/CanonicalZornRealSpinTrialityClosure.lean :: 21:namespace CanonicalZornRealSpinTrialityClosure
./lean/InfoGeometry/Canonical/CanonicalZornSpinChirality.lean :: 15:namespace CanonicalZornSpinChirality
./lean/InfoGeometry/Canonical/CanonicalZornSpinRelatedFiber.lean :: 19:namespace CanonicalZornSpinRelatedFiber
./lean/InfoGeometry/Canonical/CanonicalZornUnifiedClosure.lean :: 19:namespace CanonicalZornUnifiedClosure
./lean/InfoGeometry/Canonical/CantorTwoTreeColimitBridge.lean :: 20:namespace CantorTwoTree
./lean/InfoGeometry/Canonical/CausalDiracMatrixBasisChange.lean :: 4:namespace SplitOctonion
./lean/InfoGeometry/Canonical/CausalFunctor.lean :: 69:namespace EinsteinCausality
./lean/InfoGeometry/Canonical/CausalVortexCooperPairing.lean :: 32:namespace CausalVortex
./lean/InfoGeometry/Canonical/CausalVortexPauliEigenspaces.lean :: 16:namespace CausalVortex
./lean/InfoGeometry/Canonical/CausalVortexPauliMajorana.lean :: 18:namespace CausalVortex
./lean/InfoGeometry/Canonical/CausalVortexPauliPositivity.lean :: 17:namespace CausalVortex
./lean/InfoGeometry/Canonical/CausalVortexPauliSpectral.lean :: 16:namespace CausalVortex
./lean/InfoGeometry/Canonical/ChernSimonsGaugeInvarianceBridge.lean :: 16:namespace ChernSimonsGauge
./lean/InfoGeometry/Canonical/ChernSimonsKnotInvariant.lean :: 16:namespace ChernSimonsKnot
./lean/InfoGeometry/Canonical/ChiralCuntzSuperchargeBridge.lean :: 3:namespace ChiralCuntzSuperchargeBridge
./lean/InfoGeometry/Canonical/ChiralParitySuperalgebra.lean :: 19:namespace NoncommutativeGeometry
./lean/InfoGeometry/Canonical/CKWEntanglementMonogamyBridge.lean :: 12:namespace CKWMonogamy
./lean/InfoGeometry/Canonical/Cl11DiracOperatorConnection.lean :: 6:namespace SplitOctonion
./lean/InfoGeometry/Canonical/Cl11SheetDiracMatrices.lean :: 5:namespace SplitOctonion
./lean/InfoGeometry/Canonical/Cl11WittBasis.lean :: 4:namespace SplitOctonion
./lean/InfoGeometry/Canonical/Cl55OperatorAlgebraHom.lean :: 15:namespace NoncommutativeGeometry
./lean/InfoGeometry/Canonical/Cl55OperatorRingCatColimit.lean :: 17:namespace NoncommutativeGeometry
./lean/InfoGeometry/Canonical/CliffordCantorModeHierarchy.lean :: 14:namespace CliffordCantorModeHierarchy
./lean/InfoGeometry/Canonical/CofinalTailModularFlowTopologicalBridge.lean :: 15:namespace CStarStateColimit.Native.CofinalTailModularFlowTopologicalBridge
./lean/InfoGeometry/Canonical/CofinalTailTomitaGraphTopologicalBridge.lean :: 15:namespace CStarStateColimit.Native.CofinalTailTomitaGraphTopologicalBridge
./lean/InfoGeometry/Canonical/CompatibleStateContinuousReadout.lean :: 16:namespace CStarStateColimit.Native.ContinuousStarInductiveSystem
./lean/InfoGeometry/Canonical/ConcreteSuperVirasoroColimitReadback.lean :: 36:namespace ConcreteSuperVirasoroColimitReadback
./lean/InfoGeometry/Canonical/ConformalSubalgebraDebt.lean :: 20:namespace ConformalSubalgebra
./lean/InfoGeometry/Canonical/ConnesChernCharacterBridge.lean :: 3:namespace ConnesChern
./lean/InfoGeometry/Canonical/ConnesCocycleLogarithmicDerivative.lean :: 18:namespace ConnesCocycleLogarithm
./lean/InfoGeometry/Canonical/ConnesCyclicCohomology.lean :: 16:namespace ConnesCyclic
./lean/InfoGeometry/Canonical/ConnesLodayCyclicComplexBridge.lean :: 13:namespace ConnesLoday
./lean/InfoGeometry/Canonical/ConnesRadonNikodymCocycle.lean :: 24:namespace ConnesCocycle
./lean/InfoGeometry/Canonical/ConnesSpectral1FormAlgebra.lean :: 16:namespace ConnesSpectral1Form
./lean/InfoGeometry/Canonical/ConnesSpectralTripleBridge.lean :: 14:namespace ConnesSpectral
./lean/InfoGeometry/Canonical/ConnesTomitaModularAutomorphismBridge.lean :: 5:namespace ConnesTomita
./lean/InfoGeometry/Canonical/CStarAlgebraDirectSumBlock.lean :: 17:namespace CStarBlockAlgebra
./lean/InfoGeometry/Canonical/CStarAlgebraStateColimit.lean :: 20:namespace CStarStateColimit
./lean/InfoGeometry/Canonical/Cuntz2Isometries.lean :: 3:namespace CuntzAlgebra
./lean/InfoGeometry/Canonical/CuntzKriegerMarkovBridge.lean :: 18:namespace CuntzKriegerMarkovBridge
./lean/InfoGeometry/Canonical/CuntzNIsometries.lean :: 6:namespace CuntzAlgebra
./lean/InfoGeometry/Canonical/CuntzWordReduction.lean :: 9:namespace CuntzAlgebra
./lean/InfoGeometry/Canonical/CyclicCocycleCantor.lean :: 22:namespace CyclicCocycleCantor
./lean/InfoGeometry/Canonical/DiscreteFreeEnergyDissipationBridge.lean :: 13:namespace DiscreteThermodynamics
./lean/InfoGeometry/Canonical/DiscreteGaussBonnetKleinBridge.lean :: 9:namespace DiscreteGaussBonnetKleinBridge
./lean/InfoGeometry/Canonical/DoubledFibonacciCondensationBridge.lean :: 18:namespace DoubledFibonacciCondensationBridge
./lean/InfoGeometry/Canonical/DrinfeldCenterFibonacciBridge.lean :: 18:namespace DrinfeldCenterFibonacciBridge
./lean/InfoGeometry/Canonical/E8ExceptionalLieAlgebraTriality.lean :: 18:namespace E8ExceptionalLieAlgebraTriality
./lean/InfoGeometry/Canonical/E8LeechBridge.lean :: 11:namespace E8LeechBridge
./lean/InfoGeometry/Canonical/ETHQuantumThermalizationBridge.lean :: 16:namespace ETHThermalization
./lean/InfoGeometry/Canonical/FedosovStarProductQuantization.lean :: 16:namespace FedosovStarProduct
./lean/InfoGeometry/Canonical/FibonacciAnyonBraidingBridge.lean :: 15:namespace AnyonTopological
./lean/InfoGeometry/Canonical/FibonacciAnyonModularCategoryBridge.lean :: 17:namespace FibonacciAnyonModularCategoryBridge
./lean/InfoGeometry/Canonical/FibonacciAnyonSimilarity.lean :: 19:namespace FibonacciAnyons.Similarity
./lean/InfoGeometry/Canonical/FibonacciBraidingPhaseBridge.lean :: 16:namespace FibonacciBraidingPhaseBridge
./lean/InfoGeometry/Canonical/FibonacciCentralChargeBridge.lean :: 17:namespace FibonacciCentralChargeBridge
./lean/InfoGeometry/Canonical/FibonacciHexagonEquationBridge.lean :: 17:namespace FibonacciHexagonEquationBridge
./lean/InfoGeometry/Canonical/FibonacciModularGroupBridge.lean :: 17:namespace FibonacciModularGroupBridge
./lean/InfoGeometry/Canonical/FibonacciPentagonEquationBridge.lean :: 18:namespace FibonacciPentagonEquationBridge
./lean/InfoGeometry/Canonical/FierzModularConjugationBridge.lean :: 17:namespace FierzModularConjugationBridge
./lean/InfoGeometry/Canonical/FilteredDirectInverseColimit.lean :: 15:namespace FilteredColimit
./lean/InfoGeometry/Canonical/FilteredDualFunctionalTopologicalLimit.lean :: 14:namespace FilteredColimit.Native.TopologicalDual
./lean/InfoGeometry/Canonical/FilteredGNSAlgebraicColimitRepresentation.lean :: 17:namespace CStarStateColimit.Native.FilteredGNSAlgebraicColimitRepresentation
./lean/InfoGeometry/Canonical/FilteredGNSBoundarySpine.lean :: 19:namespace CStarStateColimit.Native.FilteredGNSBoundarySpine
./lean/InfoGeometry/Canonical/FilteredGNSBoundedGeneratorUnitaryFlow.lean :: 19:namespace CStarStateColimit.Native.FilteredGNSBoundedGeneratorUnitaryFlow
./lean/InfoGeometry/Canonical/FilteredGNSCofinalTail.lean :: 15:namespace CStarStateColimit.Native.FilteredGNSCofinalTail
./lean/InfoGeometry/Canonical/FilteredGNSCofinalTailTopCatEquivalence.lean :: 14:namespace CStarStateColimit.Native.FilteredGNSCofinalTailTopCatEquivalence
./lean/InfoGeometry/Canonical/FilteredGNSCofinalTailTopological.lean :: 20:namespace CStarStateColimit.Native.FilteredGNSCofinalTailTopological
./lean/InfoGeometry/Canonical/FilteredGNSCofinalTailTopology.lean :: 14:namespace CStarStateColimit.Native.FilteredGNSCofinalTailTopology
./lean/InfoGeometry/Canonical/FilteredGNSColimitRepresentation.lean :: 25:namespace CStarStateColimit.Native.FilteredGNSColimit
./lean/InfoGeometry/Canonical/FilteredGNSCompletionKMSState.lean :: 13:namespace CStarStateColimit.Native.FilteredGNSCompletionKMSState
./lean/InfoGeometry/Canonical/FilteredGNSFaithfulAlgebraicQuotient.lean :: 16:namespace CStarStateColimit.Native.FilteredGNSFaithfulAlgebraicQuotient
./lean/InfoGeometry/Canonical/FilteredGNSFaithfulCStarRepresentation.lean :: 16:namespace CStarStateColimit.Native.FilteredGNSFaithfulCStarRepresentation
./lean/InfoGeometry/Canonical/FilteredGNSFaithfulRangeQuotient.lean :: 20:namespace CStarStateColimit.Native.FilteredGNSFaithfulRangeQuotient
./lean/InfoGeometry/Canonical/FilteredGNSGlobalRepresentationCompatibility.lean :: 19:namespace CStarStateColimit.Native.FilteredGNSGlobalRepresentationCompatibility
./lean/InfoGeometry/Canonical/FilteredGNSGlobalStageRepresentation.lean :: 20:namespace CStarStateColimit.Native.FilteredGNSGlobalStageRepresentation
./lean/InfoGeometry/Canonical/FilteredGNSGlobalStageRepresentationTransport.lean :: 17:namespace CStarStateColimit.Native.FilteredGNSGlobalStageRepresentationTransport
./lean/InfoGeometry/Canonical/FilteredGNSHilbertColimit.lean :: 18:namespace CStarStateColimit.Native.FilteredGNSHilbertColimit
./lean/InfoGeometry/Canonical/FilteredGNSHilbertColimitTopology.lean :: 17:namespace CStarStateColimit.Native.FilteredGNSHilbertColimitTopology
./lean/InfoGeometry/Canonical/FilteredGNSHilbertNontrivial.lean :: 14:namespace CStarStateColimit.Native.FilteredGNSHilbertNontrivial
./lean/InfoGeometry/Canonical/FilteredGNSHilbertTopologicalColimitDenseRange.lean :: 13:namespace CStarStateColimit.Native.FilteredGNSHilbertColimitTopology
./lean/InfoGeometry/Canonical/FilteredGNSNormPullbackBinding.lean :: 15:namespace CStarStateColimit.Native.FilteredGNSNormPullbackBinding
./lean/InfoGeometry/Canonical/FilteredGNSOperatorConjugationTopCat.lean :: 15:namespace CStarStateColimit.Native.FilteredGNSOperatorConjugationTopCat
./lean/InfoGeometry/Canonical/FilteredGNSOperatorSeminormKernel.lean :: 16:namespace CStarStateColimit.Native.FilteredGNSOperatorSeminormKernel
./lean/InfoGeometry/Canonical/FilteredGNSRepresentation.lean :: 18:namespace CStarStateColimit.Native.FilteredGNS
./lean/InfoGeometry/Canonical/FilteredGNSRepresentationTopologicalInstantiation.lean :: 17:namespace CStarStateColimit.Native.FilteredGNSRepresentationTopologicalInstantiation
./lean/InfoGeometry/Canonical/FilteredGNSRepresentedAlgebraCompletion.lean :: 16:namespace CStarStateColimit.Native.FilteredGNSRepresentedAlgebraCompletion
./lean/InfoGeometry/Canonical/FilteredGNSRepresentedCompletionModularTransport.lean :: 20:namespace CStarStateColimit.Native.FilteredGNSRepresentedCompletionModularTransport
./lean/InfoGeometry/Canonical/FilteredGNSRepresentedCStarClosure.lean :: 17:namespace CStarStateColimit.Native.FilteredGNSRepresentedCStarClosure
./lean/InfoGeometry/Canonical/FilteredGNSRepresentedCStarCompletion.lean :: 22:namespace CStarStateColimit.Native.FilteredGNSRepresentedCStarCompletion
./lean/InfoGeometry/Canonical/FilteredGNSRepresentedCStarModularAutomorphism.lean :: 19:namespace CStarStateColimit.Native.FilteredGNSRepresentedCStarModularAutomorphism
./lean/InfoGeometry/Canonical/FilteredGNSRepresentedCStarStateCompletion.lean :: 18:namespace CStarStateColimit.Native.FilteredGNSRepresentedCStarStateCompletion
./lean/InfoGeometry/Canonical/FilteredGNSRepresentedCStarTopCatEquivalence.lean :: 14:namespace CStarStateColimit.Native.FilteredGNSRepresentedCStarTopCatEquivalence
./lean/InfoGeometry/Canonical/FilteredGNSRepresentedCStarTopology.lean :: 14:namespace CStarStateColimit.Native.FilteredGNSRepresentedCStarTopology
./lean/InfoGeometry/Canonical/FilteredGNSRepresentedRangeCompletion.lean :: 21:namespace CStarStateColimit.Native.FilteredGNSRepresentedRangeCompletion
./lean/InfoGeometry/Canonical/FilteredGNSTailRepresentation.lean :: 16:namespace CStarStateColimit.Native.FilteredGNSTailRepresentation
./lean/InfoGeometry/Canonical/FilteredGNSTailRepresentationTopology.lean :: 15:namespace CStarStateColimit.Native.FilteredGNSTailRepresentationTopology
./lean/InfoGeometry/Canonical/FilteredGNSTailStarRepresentation.lean :: 19:namespace CStarStateColimit.Native.FilteredGNSTailStarRepresentation
./lean/InfoGeometry/Canonical/FilteredGNSTomitaClosability.lean :: 19:namespace CStarStateColimit.Native.FilteredGNSTomitaClosability
./lean/InfoGeometry/Canonical/FilteredGNSTomitaClosedOperator.lean :: 19:namespace CStarStateColimit.Native.FilteredGNSTomitaClosedOperator
./lean/InfoGeometry/Canonical/FilteredGNSTomitaClosedTransport.lean :: 16:namespace CStarStateColimit.Native.FilteredGNSTomitaClosedTransport
./lean/InfoGeometry/Canonical/FilteredGNSTomitaComplexColimit.lean :: 16:namespace CStarStateColimit.Native.FilteredGNSTomitaComplexColimit
./lean/InfoGeometry/Canonical/FilteredGNSTomitaCore.lean :: 22:namespace CStarStateColimit.Native.FilteredGNSTomitaCore
./lean/InfoGeometry/Canonical/FilteredGNSTomitaDomainColimit.lean :: 17:namespace CStarStateColimit.Native.FilteredGNSTomitaDomainColimit
./lean/InfoGeometry/Canonical/FilteredGNSTomitaDomainTopologicalColimit.lean :: 16:namespace CStarStateColimit.Native.FilteredGNSTomitaDomainTopologicalColimit
./lean/InfoGeometry/Canonical/FilteredGNSTomitaGraphClosure.lean :: 19:namespace CStarStateColimit.Native.FilteredGNSTomitaGraph
./lean/InfoGeometry/Canonical/FilteredGNSTomitaGraphTopologicalColimit.lean :: 18:namespace CStarStateColimit.Native.FilteredGNSTomitaGraphTopologicalColimit
./lean/InfoGeometry/Canonical/FilteredGNSTomitaModularFormColimit.lean :: 20:namespace CStarStateColimit.Native.FilteredGNSTomitaModularFormColimit
./lean/InfoGeometry/Canonical/FilteredGNSTomitaModularForm.lean :: 21:namespace CStarStateColimit.Native.FilteredGNSTomitaModularForm
./lean/InfoGeometry/Canonical/FilteredGNSTomitaModularHilbertCompletion.lean :: 15:namespace CStarStateColimit.Native.FilteredGNSTomitaModularHilbertCompletion
./lean/InfoGeometry/Canonical/FilteredGNSTomitaModularQuotient.lean :: 14:namespace CStarStateColimit.Native.FilteredGNSTomitaModularQuotient
./lean/InfoGeometry/Canonical/FilteredGNSTomitaRealColimit.lean :: 21:namespace CStarStateColimit.Native.FilteredGNSTomitaRealColimit
./lean/InfoGeometry/Canonical/FilteredStarAlgebraActionDirectLimit.lean :: 13:namespace CStarStateColimit.Native.FilteredStarAlgebraActionDirectLimit
./lean/InfoGeometry/Canonical/FilteredStarAlgebraActionEquivDirectLimit.lean :: 15:namespace CStarStateColimit.Native.FilteredStarAlgebraActionEquivDirectLimit
./lean/InfoGeometry/Canonical/FilteredStarAlgebraActionEquivTopologicalCompatibility.lean :: 14:namespace CStarStateColimit.Native.FilteredStarAlgebraActionEquivTopologicalCompatibility
./lean/InfoGeometry/Canonical/FilteredStarAlgebraActionTopologicalCompatibility.lean :: 16:namespace CStarStateColimit.Native.FilteredStarAlgebraActionTopologicalCompatibility
./lean/InfoGeometry/Canonical/FilteredStarAlgebraAlgebraicToTopologicalColimit.lean :: 16:namespace CStarStateColimit.Native.FilteredStarAlgebraAlgebraicToTopologicalColimit
./lean/InfoGeometry/Canonical/FilteredStarAlgebraDirectLimit.lean :: 19:namespace CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
./lean/InfoGeometry/Canonical/FilteredStarAlgebraDirectLimitTopologicalCompatibility.lean :: 15:namespace CStarStateColimit.Native.FilteredStarAlgebraDirectLimitTopologicalCompatibility
./lean/InfoGeometry/Canonical/FilteredStarAlgebraDirectLimitTopologicalRealization.lean :: 17:namespace CStarStateColimit.Native.FilteredStarAlgebraDirectLimitTopologicalRealization
./lean/InfoGeometry/Canonical/FilteredStarAlgebraFiniteGroupActionDirectLimit.lean :: 14:namespace CStarStateColimit.Native.FilteredStarAlgebraFiniteGroupActionDirectLimit
./lean/InfoGeometry/Canonical/FilteredStarAlgebraFiniteGroupActionEquivDirectLimit.lean :: 13:namespace CStarStateColimit.Native.FilteredStarAlgebraFiniteGroupActionEquivDirectLimit
./lean/InfoGeometry/Canonical/FilteredStarAlgebraFiniteGroupActionTopologicalCompatibility.lean :: 16:namespace CStarStateColimit.Native.FilteredStarAlgebraFiniteGroupActionTopologicalCompatibility
./lean/InfoGeometry/Canonical/FilteredStarAlgebraTopologicalRepresentationFlow.lean :: 16:namespace CStarStateColimit.Native.FilteredStarAlgebraTopologicalRepresentationFlow
./lean/InfoGeometry/Canonical/FilteredStarAlgebraTopologicalRepresentationTransport.lean :: 17:namespace CStarStateColimit.Native.FilteredStarAlgebraTopologicalRepresentationTransport
./lean/InfoGeometry/Canonical/FilteredStarAlgebraTopologicalStarReadout.lean :: 13:namespace CStarStateColimit.Native.FilteredStarAlgebraTopologicalStarReadout
./lean/InfoGeometry/Canonical/FilteredStarAlgebraTopologicalTraceTransport.lean :: 16:namespace CStarStateColimit.Native.FilteredStarAlgebraTopologicalTraceTransport
./lean/InfoGeometry/Canonical/FilteredStarInductiveCoconeTopCat.lean :: 13:namespace CStarStateColimit.Native.ContinuousStarInductiveSystem.StarInductiveCocone
./lean/InfoGeometry/Canonical/FilteredStarInductiveSystemTopCat.lean :: 15:namespace CStarStateColimit.Native.ContinuousStarInductiveSystem
./lean/InfoGeometry/Canonical/FilteredTopologicalDirectInverseColimit.lean :: 15:namespace FilteredColimit.Native.Topological
./lean/InfoGeometry/Canonical/FQHEChiralEdgeCFTBridge.lean :: 19:namespace FQHEChiralEdgeCFTBridge
./lean/InfoGeometry/Canonical/FQHEMooreReadPfaffianBridge.lean :: 14:namespace FQHEMooreReadPfaffianBridge
./lean/InfoGeometry/Canonical/FractionalAnyonTopologicalSpin.lean :: 17:namespace FractionalAnyonSpin
./lean/InfoGeometry/Canonical/FrechetCliffordOperatorFormBridge.lean :: 17:namespace FrechetCliffordOperatorFormBridge
./lean/InfoGeometry/Canonical/FreeEnergyDissipationRate.lean :: 10:namespace MetriplecticDissipation
./lean/InfoGeometry/Canonical/FreeEnergyEquilibriumUnitaryBridge.lean :: 10:namespace MetriplecticEquilibrium
./lean/InfoGeometry/Canonical/FullOperatorBKMQuantumFisher.lean :: 17:namespace FullOperatorBKM
./lean/InfoGeometry/Canonical/GottesmanKnillStabilizerCodeBridge.lean :: 12:namespace GottesmanKnill
./lean/InfoGeometry/Canonical/HaagerupSubfactorAnyonBridge.lean :: 18:namespace HaagerupSubfactorAnyonBridge
./lean/InfoGeometry/Canonical/HaagKastlerReehSchliederAQFT.lean :: 17:namespace HaagKastlerReehSchlieder
./lean/InfoGeometry/Canonical/HaPPYPerfectTensorHolography.lean :: 18:namespace HaPPYPerfectTensorHolography
./lean/InfoGeometry/Canonical/HilbertSchmidtMatrixPairing.lean :: 14:namespace HilbertSchmidtMatrix
./lean/InfoGeometry/Canonical/HolevoQuantityChannelCapacityBridge.lean :: 15:namespace HolevoCapacity
./lean/InfoGeometry/Canonical/HolographicBekensteinHawkingUnruh.lean :: 16:namespace HolographicBekensteinHawking
./lean/InfoGeometry/Canonical/InductiveOperatorTaylorClosure.lean :: 24:namespace InductiveOperatorTaylorClosure
./lean/InfoGeometry/Canonical/IntegralZornBilinearComposition.lean :: 23:namespace IntegralZornBilinearComposition
./lean/InfoGeometry/Canonical/IntegralZornCompositionAlgebra.lean :: 15:namespace IntegralZornCompositionAlgebra
./lean/InfoGeometry/Canonical/IntegralZornII44Bridge.lean :: 24:namespace IntegralZornII44Bridge
./lean/InfoGeometry/Canonical/JackiwTeitelboimDilatonBridge.lean :: 12:namespace JackiwTeitelboim
./lean/InfoGeometry/Canonical/JarzynskiQuantumThermodynamicsBridge.lean :: 14:namespace JarzynskiThermodynamics
./lean/InfoGeometry/Canonical/JaynesFormalism.lean :: 28:namespace JaynesFormalism
./lean/InfoGeometry/Canonical/KacMoodyCurrentAlgebraBridge.lean :: 14:namespace KacMoody
./lean/InfoGeometry/Canonical/KadisonSingerStateExtension.lean :: 16:namespace KadisonSingerState
./lean/InfoGeometry/Canonical/KasparovKHomologyProductBridge.lean :: 17:namespace KasparovKHomologyProductBridge
./lean/InfoGeometry/Canonical/KasparovKKTheoryBivariantBridge.lean :: 10:namespace FiniteContinuousBivariantModel
./lean/InfoGeometry/Canonical/KitaevBdGPfaffianBridge.lean :: 14:namespace KitaevBdGPfaffianBridge
./lean/InfoGeometry/Canonical/KitaevChainTopologicalZ2Invariant.lean :: 17:namespace KitaevChainTopologicalZ2Invariant
./lean/InfoGeometry/Canonical/KitaevCliffordBridge.lean :: 4:namespace KitaevCliffordBridge
./lean/InfoGeometry/Canonical/KitaevHoneycombPlaquetteFluxBridge.lean :: 17:namespace KitaevHoneycombPlaquetteFluxBridge
./lean/InfoGeometry/Canonical/KitaevQuantumDoubleGSDBridge.lean :: 6:namespace KitaevQuantumDoubleGSDBridge
./lean/InfoGeometry/Canonical/KitaevSpinLiquidHoneycombBridge.lean :: 12:namespace KitaevSpinLiquid
./lean/InfoGeometry/Canonical/KleinBottleMoebiusToricCodeBridge.lean :: 17:namespace KleinBottleMoebiusToricCodeBridge
./lean/InfoGeometry/Canonical/KMSBoundaryTrajectory.lean :: 55:namespace KMSBoundaryTrajectory
./lean/InfoGeometry/Canonical/KuboMoriBogoliubovMetric.lean :: 17:namespace KuboMoriBogoliubov
./lean/InfoGeometry/Canonical/LaughlinStateQuantumHallBridge.lean :: 15:namespace QuantumHall
./lean/InfoGeometry/Canonical/LevinWenStringNetTopologicalEntropy.lean :: 16:namespace LevinWenStringNet
./lean/InfoGeometry/Canonical/LiHaldaneEntanglementSpectrumBridge.lean :: 16:namespace LiHaldane
./lean/InfoGeometry/Canonical/MajoranaBraidingCliffordBridge.lean :: 18:namespace MajoranaBraidingCliffordBridge
./lean/InfoGeometry/Canonical/MajoranaZeroModeParity.lean :: 17:namespace MajoranaParity
./lean/InfoGeometry/Canonical/MatrixAlgebraCuntzEmbedding.lean :: 10:namespace CuntzAlgebra
./lean/InfoGeometry/Canonical/MERATensorNetworkHolographyBridge.lean :: 14:namespace MERAHolography
./lean/InfoGeometry/Canonical/MetriplecticDissipativeSystem.lean :: 16:namespace MetriplecticSystem
./lean/InfoGeometry/Canonical/ModularSpectralAsymmetryBridge.lean :: 16:namespace ModularSpectral
./lean/InfoGeometry/Canonical/ModularZ2CubeGrading.lean :: 10:namespace ModularZ2CubeGrading
./lean/InfoGeometry/Canonical/MontonenOliveSDualityDiracQuantization.lean :: 17:namespace MontonenOliveSDualityDiracQuantization
./lean/InfoGeometry/Canonical/MooreReadPfaffianFractionalHall.lean :: 17:namespace MooreReadPfaffianFractionalHall
./lean/InfoGeometry/Canonical/MultiChainUHFEmbedding.lean :: 10:namespace MultiChainUHF
./lean/InfoGeometry/Canonical/NambuGorkovParticleHoleBridge.lean :: 16:namespace NambuGorkovParticleHoleBridge
./lean/InfoGeometry/Canonical/NonAbelianBerryPhaseBridge.lean :: 14:namespace NonAbelianBerry
./lean/InfoGeometry/Canonical/NonAbelianGaugeBianchiIdentity.lean :: 16:namespace NonAbelianGauge
./lean/InfoGeometry/Canonical/NonCommutativeJordanAlgebra.lean :: 16:namespace NonCommutativeJordan
./lean/InfoGeometry/Canonical/NoncommutativeTorusAlgebraBridge.lean :: 15:namespace NoncommutativeTorusAlgebraBridge
./lean/InfoGeometry/Canonical/NonCommutativeTorusMoritaBridge.lean :: 15:namespace NonCommutativeTorus
./lean/InfoGeometry/Canonical/NormalizedTraceCauchySchwarz.lean :: 12:namespace NormalizedTraceCauchySchwarz
./lean/InfoGeometry/Canonical/NormalizedTraceCyclicity.lean :: 7:namespace NormalizedTraceCyclicity
./lean/InfoGeometry/Canonical/NormalizedTraceInvariance.lean :: 10:namespace MultiChainNormalizedTrace
./lean/InfoGeometry/Canonical/NormalizedTracePositivity.lean :: 11:namespace NormalizedTracePositivity
./lean/InfoGeometry/Canonical/OperatorGradedAdjointLift.lean :: 28:namespace NoncommutativeGeometry
./lean/InfoGeometry/Canonical/OperatorPin55Action.lean :: 14:namespace NoncommutativeGeometry
./lean/InfoGeometry/Canonical/OperatorTKKAnomalyAnnihilation.lean :: 14:namespace NoncommutativeGeometry
./lean/InfoGeometry/Canonical/OTOCScramblingChaosBridge.lean :: 16:namespace OTOCScrambling
./lean/InfoGeometry/Canonical/PeirceDeWittIdealModularBridge.lean :: 17:namespace PeirceDeWittIdeal
./lean/InfoGeometry/Canonical/_PeirceScratch.lean :: 2:namespace Test
./lean/InfoGeometry/Canonical/PhysicalBdGPairingBridge.lean :: 42:namespace PhysicalBdGPairingBridge
./lean/InfoGeometry/Canonical/PrimeCocycleCoefficients.lean :: 32:namespace PrimeCocycleCoefficients
./lean/InfoGeometry/Canonical/ProjectiveAffineConformalClosure55.lean :: 20:namespace ProjectiveAffineConformalClosure55
./lean/InfoGeometry/Canonical/QuantumChannelContractivity.lean :: 23:namespace QuantumChannelContractivity
./lean/InfoGeometry/Canonical/QuantumDoubleS3Bridge.lean :: 17:namespace QuantumDoubleS3Bridge
./lean/InfoGeometry/Canonical/QuantumDoubleToricCodeBridge.lean :: 17:namespace QuantumDoubleToricCodeBridge
./lean/InfoGeometry/Canonical/QuantumGroupHopfAlgebra.lean :: 16:namespace QuantumGroupHopf
./lean/InfoGeometry/Canonical/QuantumGroupUqSL2Bridge.lean :: 13:namespace QuantumGroupUqSL2Bridge
./lean/InfoGeometry/Canonical/QuantumHallChernNumber.lean :: 16:namespace QuantumHallChern
./lean/InfoGeometry/Canonical/QuantumHallSkyrmionBridge.lean :: 14:namespace QuantumHallSkyrmionBridge
./lean/InfoGeometry/Canonical/QuantumHallSkyrmionTopologicalCharge.lean :: 17:namespace QuantumHallSkyrmionTopologicalCharge
./lean/InfoGeometry/Canonical/QuantumInformationBottleneckBridge.lean :: 15:namespace QuantumInformation
./lean/InfoGeometry/Canonical/QuantumRelativeEntropyMonotonicity.lean :: 18:namespace QuantumRelativeEntropy
./lean/InfoGeometry/Canonical/QuantumRelativeSurprisal.lean :: 14:namespace QuantumRelativeSurprisal
./lean/InfoGeometry/Canonical/QuantumTransportCoefficientBridge.lean :: 12:namespace QuantumTransport
./lean/InfoGeometry/Canonical/RealSplitOctFiveGradeProjectiveBridge.lean :: 15:namespace CanonicalZornFiveGradedClosure
./lean/InfoGeometry/Canonical/SE2CompactAffineOrbit.lean :: 12:namespace SE2Souriau.CompactRotation
./lean/InfoGeometry/Canonical/SE2SouriauCoadjointOrbit.lean :: 10:namespace SE2Souriau
./lean/InfoGeometry/Canonical/SE2SouriauCoadjointTopology.lean :: 16:namespace SE2Souriau
./lean/InfoGeometry/Canonical/SE2SouriauCompactOrbit.lean :: 6:namespace SE2Souriau.CompactRotation
./lean/InfoGeometry/Canonical/SeibergWittenGaugeMapBridge.lean :: 12:namespace SeibergWitten
./lean/InfoGeometry/Canonical/SimplexSurprisalMetriplectic.lean :: 39:namespace SimplexState
./lean/InfoGeometry/Canonical/SkyrmionPontryaginTopologicalChargeBridge.lean :: 12:namespace SkyrmionTopology
./lean/InfoGeometry/Canonical/SL2RToG2WiesbrockEmbedding.lean :: 17:namespace SL2RToG2Wiesbrock
./lean/InfoGeometry/Canonical/SolderingQuaternionicGaugeBianchiBridge.lean :: 19:namespace SolderingQuaternionicGauge
./lean/InfoGeometry/Canonical/SouriauBregmanLegendreBridge.lean :: 11:namespace SouriauBregman
./lean/InfoGeometry/Canonical/SouriauBuresWassersteinBridge.lean :: 17:namespace SouriauBuresWasserstein
./lean/InfoGeometry/Canonical/SouriauCoadjointCovariance.lean :: 6:namespace SouriauCoadjoint
./lean/InfoGeometry/Canonical/SouriauCoadjointFisherRaoEquivalence.lean :: 16:namespace SouriauPoincare
./lean/InfoGeometry/Canonical/SouriauCoadjointOrbitSymplecticReduction.lean :: 7:namespace SouriauReduction
./lean/InfoGeometry/Canonical/SouriauHellingerSquareRootBridge.lean :: 13:namespace SouriauHellinger
./lean/InfoGeometry/Canonical/SouriauHilbertSchmidtOnsager.lean :: 8:namespace SouriauHilbertSchmidtOnsager
./lean/InfoGeometry/Canonical/SouriauInformationCurvatureTensor.lean :: 12:namespace SouriauCurvature
./lean/InfoGeometry/Canonical/SouriauKahlerCoadjointBridge.lean :: 13:namespace SouriauKahler
./lean/InfoGeometry/Canonical/SouriauKKSForm.lean :: 13:namespace SouriauKKS
./lean/InfoGeometry/Canonical/SouriauMetriplecticBracket.lean :: 17:namespace SouriauMetriplectic
./lean/InfoGeometry/Canonical/SouriauOnsagerBKMBridge.lean :: 6:namespace SouriauOnsagerBKM
./lean/InfoGeometry/Canonical/SouriauOnsagerBKMIntegrabilityAdapter.lean :: 12:namespace SouriauOnsagerBKM
./lean/InfoGeometry/Canonical/SouriauOnsagerBKMIntegrability.lean :: 14:namespace SouriauOnsagerBKM
./lean/InfoGeometry/Canonical/SouriauOnsagerBKMRealForm.lean :: 6:namespace SouriauOnsagerBKM
./lean/InfoGeometry/Canonical/SouriauQuantumCramerRaoHelstromBridge.lean :: 13:namespace SouriauQuantumCramerRao
./lean/InfoGeometry/Canonical/SouriauRelativeEntropyBandTopology.lean :: 3:namespace SouriauRelativeEntropyBandTopology
./lean/InfoGeometry/Canonical/SouriauRelativeEntropyFisherBridge.lean :: 17:namespace SouriauRelativeEntropy
./lean/InfoGeometry/Canonical/SouriauRelativeEntropyLevelTopology.lean :: 3:namespace SouriauRelativeEntropyLevelTopology
./lean/InfoGeometry/Canonical/SouriauRelativeEntropyPersistenceBifiltration.lean :: 3:namespace SouriauRelativeEntropyPersistenceBifiltration
./lean/InfoGeometry/Canonical/SouriauRelativeEntropyPersistenceColimit.lean :: 5:namespace SouriauRelativeEntropyPersistenceColimit
./lean/InfoGeometry/Canonical/SouriauRelativeEntropyPersistenceComparisonIndependence.lean :: 3:namespace SouriauRelativeEntropyPersistenceComparisonIndependence
./lean/InfoGeometry/Canonical/SouriauRelativeEntropyPersistenceCutoffFunctor.lean :: 3:namespace SouriauRelativeEntropyPersistenceCutoffFunctor
./lean/InfoGeometry/Canonical/SouriauRelativeEntropyPersistenceCutoff.lean :: 3:namespace SouriauRelativeEntropyPersistenceCutoff
./lean/InfoGeometry/Canonical/SouriauRelativeEntropyPersistenceCutoffLimit.lean :: 3:namespace SouriauRelativeEntropyPersistenceCutoffLimit
./lean/InfoGeometry/Canonical/SouriauRelativeEntropyPersistenceDiagram.lean :: 4:namespace SouriauRelativeEntropyPersistenceDiagram
./lean/InfoGeometry/Canonical/SouriauRelativeEntropyPersistenceFunctor.lean :: 3:namespace SouriauRelativeEntropyPersistenceFunctor
./lean/InfoGeometry/Canonical/SouriauRelativeEntropyPersistenceLimitColimitComparison.lean :: 3:namespace SouriauRelativeEntropyPersistenceLimitColimitComparison
./lean/InfoGeometry/Canonical/SouriauRelativeEntropyPersistenceMixedComparison.lean :: 3:namespace SouriauRelativeEntropyPersistenceMixedComparison
./lean/InfoGeometry/Canonical/SouriauRelativeEntropyPersistenceQuotient.lean :: 3:namespace SouriauRelativeEntropyPersistenceQuotient
./lean/InfoGeometry/Canonical/SouriauRelativeEntropyPersistenceUniversal.lean :: 3:namespace SouriauRelativeEntropyPersistenceUniversal
./lean/InfoGeometry/Canonical/SouriauRelativeEntropySimplexTopology.lean :: 7:namespace SouriauRelativeEntropySimplex
./lean/InfoGeometry/Canonical/SouriauRelativeEntropySublevelDiagram.lean :: 3:namespace SouriauRelativeEntropySublevelDiagram
./lean/InfoGeometry/Canonical/SouriauRelativeEntropySublevelTopology.lean :: 3:namespace SouriauRelativeEntropySublevel
./lean/InfoGeometry/Canonical/SouriauWassersteinGradientFlow.lean :: 11:namespace SouriauWasserstein
./lean/InfoGeometry/Canonical/SplitOctonionAlternativeLaws.lean :: 6:namespace SplitOctonion
./lean/InfoGeometry/Canonical/SplitOctonionConjugation.lean :: 6:namespace SplitOctonion
./lean/InfoGeometry/Canonical/SplitOctonionDoubledLoxodromic.lean :: 7:namespace SplitOctonion
./lean/InfoGeometry/Canonical/SplitOctonionDoubledLoxodromicSpectral.lean :: 14:namespace SplitOctonion
./lean/InfoGeometry/Canonical/SplitOctonionExpLog.lean :: 7:namespace SplitOctonion
./lean/InfoGeometry/Canonical/SplitOctonionHyperbolicFunctionalCalculus.lean :: 16:namespace SplitOctonion
./lean/InfoGeometry/Canonical/SplitOctonionHyperbolicPolarStructure.lean :: 10:namespace SplitOctonion
./lean/InfoGeometry/Canonical/SplitOctonionHyperbolicSpectralProjectors.lean :: 10:namespace SplitOctonion
./lean/InfoGeometry/Canonical/SplitOctonionLoxodromicCircularBridge.lean :: 10:namespace SplitOctonion
./lean/InfoGeometry/Canonical/SplitOctonionPolarTransport.lean :: 15:namespace SplitOctonion
./lean/InfoGeometry/Canonical/SplitOctonionQuaternionChart.lean :: 12:namespace SplitOctonion
./lean/InfoGeometry/Canonical/SplitOctonionQuaternionPolar.lean :: 9:namespace SplitOctonion
./lean/InfoGeometry/Canonical/SplitOctonionRegularEllipticOperators.lean :: 7:namespace SplitOctonion
./lean/InfoGeometry/Canonical/SplitOctonionRegularNormOperators.lean :: 6:namespace SplitOctonion
./lean/InfoGeometry/Canonical/SplitOctonionRegularOperators.lean :: 6:namespace SplitOctonion
./lean/InfoGeometry/Canonical/SplitOctonionRegularParabolicOperators.lean :: 6:namespace SplitOctonion
./lean/InfoGeometry/Canonical/SplitOctonionRegularProjectors.lean :: 7:namespace SplitOctonion
./lean/InfoGeometry/Canonical/SplitQuaternionCayleyZornBridge.lean :: 18:namespace SplitQuaternionZorn
./lean/InfoGeometry/Canonical/StarAlgEquivPullback.lean :: 15:namespace StarAlgEquivPullback
./lean/InfoGeometry/Canonical/StarAlgEquivTransport.lean :: 11:namespace StarAlgEquivTransport
./lean/InfoGeometry/Canonical/SYKQuantumScramblingBridge.lean :: 12:namespace SYKScrambling
./lean/InfoGeometry/Canonical/TemperleyLiebJonesBridge.lean :: 13:namespace TemperleyLiebJonesBridge
./lean/InfoGeometry/Canonical/TensorNetworkHolography.lean :: 18:namespace TensorNetworkHolography
./lean/InfoGeometry/Canonical/ThermofieldDoubleFreeEnergyEntropy.lean :: 17:namespace ThermofieldDoubleFreeEnergyEntropy
./lean/InfoGeometry/Canonical/TKKJordanPairData.lean :: 22:namespace TKKJordanPairData
./lean/InfoGeometry/Canonical/TomitaTakesakiKMSEntropyBracket.lean :: 13:namespace TomitaTakesakiKMSEntropy
./lean/InfoGeometry/Canonical/TomitaTakesakiModularCocycle.lean :: 17:namespace TomitaTakesakiCocycle
./lean/InfoGeometry/Canonical/TomitaTakesakiTFDModularOperator.lean :: 24:namespace QuantumSystem
./lean/InfoGeometry/Canonical/TomitaTakesakiWiesbrockZornBridge.lean :: 18:namespace TomitaTakesakiWiesbrock
./lean/InfoGeometry/Canonical/TopologicalEntanglementEntropyBridge.lean :: 19:namespace TopologicalEntanglementEntropyBridge
./lean/InfoGeometry/Canonical/TopologicalInsulatorZ2Bridge.lean :: 12:namespace TopologicalInsulator
./lean/InfoGeometry/Canonical/TopologicalModularFormsEllipticGenera.lean :: 17:namespace TopologicalModularFormsEllipticGenera
./lean/InfoGeometry/Canonical/ToricCodeTwistDefectIsingBridge.lean :: 17:namespace ToricCodeTwistDefectIsingBridge
./lean/InfoGeometry/Canonical/UHFColimitSuperchargeBridge.lean :: 29:namespace NoncommutativeGeometry
./lean/InfoGeometry/Canonical/UHFColimitTKKAnomalyBridge.lean :: 31:namespace NoncommutativeGeometry
./lean/InfoGeometry/Canonical/UHFDirectLimitCARAlgebra.lean :: 16:namespace UHFDirectLimitCAR
./lean/InfoGeometry/Canonical/UnitTraceNormalization.lean :: 7:namespace UnitTraceNormalization
./lean/InfoGeometry/Canonical/VerlindeFormulaFibonacciBridge.lean :: 17:namespace VerlindeFormulaFibonacciBridge
./lean/InfoGeometry/Canonical/ViazovskaMagicFunctionBridge.lean :: 14:namespace ViazovskaMagicFunctionBridge
./lean/InfoGeometry/Canonical/WessZuminoGaugeConsistency.lean :: 16:namespace WessZuminoGauge
./lean/InfoGeometry/Canonical/WessZuminoWittenAnomalyBridge.lean :: 12:namespace WessZuminoWitten
./lean/InfoGeometry/Canonical/WeylCantorSynthesis.lean :: 57:namespace WeylCantorSynthesis
./lean/InfoGeometry/Canonical/WeylIntegrationFixedPoint.lean :: 65:namespace WeylIntegrationFixedPoint
./lean/InfoGeometry/Canonical/WiesbrockLieBracketCommutator.lean :: 16:namespace LieBracketCommutator
./lean/InfoGeometry/Canonical/WiesbrockSUSYPoincareBridge.lean :: 15:namespace SuperWiesbrock
./lean/InfoGeometry/Canonical/ZornCartanTorusLaplaceMellin.lean :: 6:namespace ZornCore
./lean/InfoGeometry/Canonical/ZornCayleyDicksonIsomorphism.lean :: 17:namespace ZornCayleyDickson
./lean/InfoGeometry/Canonical/ZornCellComposition.lean :: 24:namespace ZornCell
./lean/InfoGeometry/Canonical/ZornCore.lean :: 13:namespace ZornCore
./lean/InfoGeometry/Canonical/ZornOctonionAnyonGellMannBridge.lean :: 18:namespace ZornOctonionAnyon
./lean/InfoGeometry/Canonical/ZornOuterTrialityGroup.lean :: 11:namespace ZornOuterTrialityGroup
./lean/InfoGeometry/Canonical/ZornSuperchargeBoundaryCommutantBridge.lean :: 18:namespace ZornSupercharge
./lean/InfoGeometry/Canonical/ZornTrialityTKKBridge.lean :: 20:namespace ZornTrialityTKKBridge
./lean/InfoGeometry/Categorical/CFTPrimary.lean :: 5:namespace PrimaryState
./lean/InfoGeometry/Categorical/ZornBraidColimitKMS.lean :: 51:namespace ZornBraidColimitKMS
./lean/InfoGeometry/DeterminantTrifactor.lean :: 18:namespace DeterminantTrifactor
./lean/InfoGeometry/ErlangenCoordinateless.lean :: 36:namespace ErlangenCoordinateless
./lean/InfoGeometry/Eval/SeedProverSmoke.lean :: 5:namespace SeedProverSmoke
./lean/InfoGeometry/Experimental/WeylCantorFock.lean :: 47:namespace WeylCantorFock
./lean/InfoGeometry/Experimental/WeylIntegrationFormula.lean :: 61:namespace WeylIntegration
./lean/InfoGeometry/External/Auto/A35MirrorNuclei.lean :: 3:namespace A35MirrorNuclei
./lean/InfoGeometry/External/Auto/A47MirrorNuclei.lean :: 6:namespace A47MirrorNuclei
./lean/InfoGeometry/External/Auto/A67MirrorE1.lean :: 3:namespace A67MirrorE1
./lean/InfoGeometry/External/Auto/AdelicDiracOperator.lean :: 3:namespace AdelicDiracOperator
./lean/InfoGeometry/External/Auto/AffineDynkinGoutevTonev.lean :: 23:namespace AffineDynkinGoutevTonev
./lean/InfoGeometry/External/Auto/AlgebraicCuntzToeplitzInductive.lean :: 18:namespace AlgebraicCuntzToeplitzInductive
./lean/InfoGeometry/External/Auto/AmariChentsovFierzTorsion.lean :: 16:namespace AmariChentsovFierzTorsion
./lean/InfoGeometry/External/Auto/AnomalousKMSFlow.lean :: 9:namespace AnomalousKMSFlow
./lean/InfoGeometry/External/Auto/AnomalyInverses.lean :: 5:namespace VarlamovAnomaly
./lean/InfoGeometry/External/Auto/ArangoBrainMetaprogram.lean :: 8:namespace AgentBrain
./lean/InfoGeometry/External/Auto/AssociativeCommutatorLie.lean :: 5:namespace AssociativeCommutatorLie
./lean/InfoGeometry/External/Auto/B3RepresentationBridge.lean :: 18:namespace B3RepresentationBridge
./lean/InfoGeometry/External/Auto/BiquaternionCliffordIso.lean :: 16:namespace BiquaternionCliffordIso
./lean/InfoGeometry/External/Auto/BiquaternionExpClosure.lean :: 23:namespace BiquaternionExpClosure
./lean/InfoGeometry/External/Auto/BiquaternionKANnilpotent.lean :: 7:namespace BiquaternionKANnilpotent
./lean/InfoGeometry/External/Auto/BiquaternionMobiusSquashing.lean :: 13:namespace BiquaternionMobiusSquashing
./lean/InfoGeometry/External/Auto/BiquaternionNegativeRootsLog.lean :: 16:namespace BiquaternionNegativeRootsLog
./lean/InfoGeometry/External/Auto/BirkhoffInformationGeometry.lean :: 3:namespace BirkhoffInformationGeometry
./lean/InfoGeometry/External/Auto/BisoiForbiddenE1Mixing.lean :: 5:namespace BisoiForbiddenE1Mixing
./lean/InfoGeometry/External/Auto/BizzetiA67IVGMR.lean :: 5:namespace BizzetiA67IVGMR
./lean/InfoGeometry/External/Auto/BlackHoleHolography.lean :: 15:namespace BlackHoleHolography
./lean/InfoGeometry/External/Auto/BM1MirrorNuclei.lean :: 13:namespace BM1MirrorNuclei
./lean/InfoGeometry/External/Auto/BogoliubovBraidGraphWeld.lean :: 23:namespace BogoliubovBraidGraphWeld
./lean/InfoGeometry/External/Auto/BostConnesDeformation.lean :: 8:namespace BostConnesDeformation
./lean/InfoGeometry/External/Auto/BPSPositiveEnergyBound.lean :: 5:namespace BPSPositiveEnergyBound
./lean/InfoGeometry/External/Auto/BraidedCocycleWilsonEntropy.lean :: 11:namespace BraidedCocycleWilsonEntropy
./lean/InfoGeometry/External/Auto/BraidInductiveColimitCategory.lean :: 18:namespace BraidInductiveColimitComplement
./lean/InfoGeometry/External/Auto/BraidInductiveColimitComplement.lean :: 22:namespace BraidInductiveColimitComplement
./lean/InfoGeometry/External/Auto/BrillouinKleinNilpotentAttractor.lean :: 18:namespace BrillouinKleinNilpotentAttractor
./lean/InfoGeometry/External/Auto/BuresInformationGeodesicFlow.lean :: 22:namespace BuresInformationGeodesicFlow
./lean/InfoGeometry/External/Auto/CakirliPnInteractionIsospin.lean :: 5:namespace CakirliPnInteractionIsospin
./lean/InfoGeometry/External/Auto/CanonicalSouriauPauliThermodynamics.lean :: 16:namespace CanonicalSouriauPauliThermodynamics
./lean/InfoGeometry/External/Auto/CARCCRCantorFock.lean :: 27:namespace CARCCRCantorFock
./lean/InfoGeometry/External/Auto/CartanTriality.lean :: 13:namespace CartanTriality
./lean/InfoGeometry/External/Auto/CartanWeylBogoliubovGravity.lean :: 20:namespace CartanWeylBogoliubovGravity
./lean/InfoGeometry/External/Auto/CasimirIsospinHamiltonian.lean :: 5:namespace CasimirIsospinHamiltonian
./lean/InfoGeometry/External/Auto/CausalPosetEntropy.lean :: 15:namespace CausalPoset
./lean/InfoGeometry/External/Auto/CausalStructure.lean :: 24:namespace GloballyHyperbolic
./lean/InfoGeometry/External/Auto/CayleyHilbertPolyaBraid.lean :: 14:namespace LegacyCayleyHilbertPolyaBraid
./lean/InfoGeometry/External/Auto/CayleySchreierGauge.lean :: 12:namespace CayleySchreierGauge
./lean/InfoGeometry/External/Auto/ChemicalPotentialMetricBridge.lean :: 12:namespace ChemicalPotentialMetricBridge
./lean/InfoGeometry/External/Auto/ChiralAffineBogoliubovWeld.lean :: 24:namespace ChiralAffineBogoliubovWeld
./lean/InfoGeometry/External/Auto/ChiralCuntzInductive.lean :: 20:namespace ChiralCuntzInductive
./lean/InfoGeometry/External/Auto/ChiralTwistedFibration.lean :: 306:namespace Transport
./lean/InfoGeometry/External/Auto/CliffordInductiveTripotent.lean :: 13:namespace CliffordInductiveTripotent
./lean/InfoGeometry/External/Auto/CoherentOrbitalPrecession.lean :: 26:namespace CoherentOrbitalPrecession
./lean/InfoGeometry/External/Auto/CompleteHolographicDictionary.lean :: 18:namespace CompleteHolographicDictionary
./lean/InfoGeometry/External/Auto/ConnesMarcolliShimura.lean :: 36:namespace ConcreteShimuraModel
./lean/InfoGeometry/External/Auto/ConnesSpectralAction.lean :: 6:namespace ConnesSpectralAction
./lean/InfoGeometry/External/Auto/ContinuumAsColimitCounting.lean :: 22:namespace ContinuumAsColimitCounting
./lean/InfoGeometry/External/Auto/ConvexAlgebraicDuality.lean :: 18:namespace ConvexAlgebraicDuality
./lean/InfoGeometry/External/Auto/CooperadEnvironmentalRank32.lean :: 12:namespace CooperadEnvironmentalRank32
./lean/InfoGeometry/External/Auto/CPTCausalCone.lean :: 7:namespace CPTCausalCone
./lean/InfoGeometry/External/Auto/CPTDeRhamCohomology.lean :: 9:namespace CPTDeRham
./lean/InfoGeometry/External/Auto/CptFractalClosure.lean :: 10:namespace CptFractalClosure
./lean/InfoGeometry/External/Auto/CPTKreinTowerBridge.lean :: 23:namespace CPTKreinTowerBridge
./lean/InfoGeometry/External/Auto/CptTensorFractal.lean :: 12:namespace CptTensorFractal
./lean/InfoGeometry/External/Auto/CubicJordanPeirceDecomposition.lean :: 14:namespace CubicJordanPeirceDecomposition
./lean/InfoGeometry/External/Auto/CuntzBraidCantor.lean :: 3:namespace CuntzBraidCantor
./lean/InfoGeometry/External/Auto/CuntzK0TorsionRelation.lean :: 5:namespace CuntzK0TorsionRelation
./lean/InfoGeometry/External/Auto/CuntzKriegerFibonacciK.lean :: 23:namespace CuntzKriegerFibonacciK
./lean/InfoGeometry/External/Auto/CuntzKriegerKTheory.lean :: 14:namespace CuntzKriegerKTheory
./lean/InfoGeometry/External/Auto/CuntzKTheoryPairing.lean :: 8:namespace CuntzKTheoryPairing
./lean/InfoGeometry/External/Auto/CuntzZornEntropy.lean :: 19:namespace BogoliubovTransform
./lean/InfoGeometry/External/Auto/D4TrialityUniverse.lean :: 23:namespace D4TrialityUniverse
./lean/InfoGeometry/External/Auto/determinant_weyl_gauge.lean :: 128:namespace Twistor
./lean/InfoGeometry/External/Auto/DikinGoutevTonevBridge.lean :: 19:namespace DikinGoutevTonevBridge
./lean/InfoGeometry/External/Auto/DiracFourierMellin.lean :: 10:namespace DiracFourierMellin
./lean/InfoGeometry/External/Auto/DiracKreinMetriplectic.lean :: 20:namespace DiracKreinMetriplectic
./lean/InfoGeometry/External/Auto/DiracResolventZeroModeTripotent.lean :: 21:namespace DiracResolventZeroModeTripotent
./lean/InfoGeometry/External/Auto/DiracZeroModes.lean :: 12:namespace DiracZeroModes
./lean/InfoGeometry/External/Auto/discrete_maxflow_mincut.lean :: 3:namespace DiscreteMaxFlowMinCut
./lean/InfoGeometry/External/Auto/DupontHypersurfaceOSModel.lean :: 18:namespace DupontHypersurfaceOSModel
./lean/InfoGeometry/External/Auto/EinsteinThermodynamicBridge.lean :: 13:namespace EinsteinThermodynamicBridge
./lean/InfoGeometry/External/Auto/ExceptionalKleinGlideEP.lean :: 16:namespace ExceptionalKleinGlideEP
./lean/InfoGeometry/External/Auto/ExceptionalNonorientableTopology.lean :: 26:namespace ExceptionalNonorientableTopology
./lean/InfoGeometry/External/Auto/ExceptionalTopologicalBandStructures.lean :: 20:namespace ExceptionalTopologicalBandStructures
./lean/InfoGeometry/External/Auto/FarneaGe64IsospinMixing.lean :: 12:namespace FarneaGe64IsospinMixing
./lean/InfoGeometry/External/Auto/FibAnyonThm7_hexagon.lean :: 6:namespace FibAnyonThm7Hexagon
./lean/InfoGeometry/External/Auto/FiniteArithmeticUHFTrace.lean :: 20:namespace FiniteArithmeticUHFTrace
./lean/InfoGeometry/External/Auto/FiniteDirichletOccupation.lean :: 23:namespace FiniteDirichletOccupation
./lean/InfoGeometry/External/Auto/FiniteGNSConstruction.lean :: 5:namespace FiniteGNSConstruction
./lean/InfoGeometry/External/Auto/FiniteMatrixElementDuality.lean :: 21:namespace FiniteMatrixElementDuality
./lean/InfoGeometry/External/Auto/FiniteMobiusCoefficient.lean :: 17:namespace FiniteMobiusCoefficient
./lean/InfoGeometry/External/Auto/FinitePrimeFock.lean :: 24:namespace FinitePrimeFock
./lean/InfoGeometry/External/Auto/FiniteProjectorSpectralCalculus.lean :: 5:namespace FiniteProjectorSpectralCalculus
./lean/InfoGeometry/External/Auto/FiniteUHFBooleanTrace.lean :: 20:namespace FiniteUHFBooleanTrace
./lean/InfoGeometry/External/Auto/FixedLineRiemannKlein.lean :: 18:namespace FixedLineRiemannKlein
./lean/InfoGeometry/External/Auto/FockUHFBridge.lean :: 20:namespace FockUHFBridge
./lean/InfoGeometry/External/Auto/FractalHamiltonian.lean :: 11:namespace FractalHamiltonian
./lean/InfoGeometry/External/Auto/FractalKleinSUSYFramework.lean :: 16:namespace FractalKleinSUSYFramework
./lean/InfoGeometry/External/Auto/FredholmModularRegularization.lean :: 26:namespace FredholmModularRegularization
./lean/InfoGeometry/External/Auto/FredholmRegularization.lean :: 18:namespace FredholmRegularization
./lean/InfoGeometry/External/Auto/FreedAnomalyCancellation.lean :: 1:namespace Freed
./lean/InfoGeometry/External/Auto/GellMannCartan.lean :: 13:namespace GellMannCartan
./lean/InfoGeometry/External/Auto/GeneralizedMirrorNuclei.lean :: 16:namespace GeneralizedMirrorNuclei
./lean/InfoGeometry/External/Auto/GeometricZeta.lean :: 33:namespace SplitParavector
./lean/InfoGeometry/External/Auto/GlideDiracSelectionRule.lean :: 20:namespace GlideDiracSelectionRule
./lean/InfoGeometry/External/Auto/GlideModularJ.lean :: 18:namespace GlideModularJ
./lean/InfoGeometry/External/Auto/GlideSuperchargeCasimir.lean :: 17:namespace GlideSuperchargeCasimir
./lean/InfoGeometry/External/Auto/GlideSymmetricInvariant.lean :: 13:namespace GlideSymmetricInvariant
./lean/InfoGeometry/External/Auto/GNSConstruction.lean :: 52:namespace State
./lean/InfoGeometry/External/Auto/GNSModularObservables.lean :: 20:namespace GNSModularObservables
./lean/InfoGeometry/External/Auto/GNSQuotientFinite.lean :: 18:namespace GNSQuotientFinite
./lean/InfoGeometry/External/Auto/GohbergKreinIndex.lean :: 13:namespace GohbergKreinIndex
./lean/InfoGeometry/External/Auto/GoldenCCR.lean :: 15:namespace GoldenCCR
./lean/InfoGeometry/External/Auto/GoldenSpectralTriple.lean :: 13:namespace GoldenSpectralTriple
./lean/InfoGeometry/External/Auto/goutev_principle.lean :: 4:namespace GoutevPrinciple
./lean/InfoGeometry/External/Auto/GoutevTonevPrinciple.lean :: 20:namespace GoutevTonevPrinciple
./lean/InfoGeometry/External/Auto/GrandHolographicTheorem.lean :: 19:namespace GrandHolographicTheorem
./lean/InfoGeometry/External/Auto/GravitySoldering.lean :: 12:namespace GravitySoldering
./lean/InfoGeometry/External/Auto/GT_FromText.lean :: 17:namespace GT.Extracted
./lean/InfoGeometry/External/Auto/GuptaAdaptVQERandomHamiltonians.lean :: 5:namespace GuptaAdaptVQERandomHamiltonians
./lean/InfoGeometry/External/Auto/HeavyIsospinMixingSystematics.lean :: 7:namespace HeavyIsospinMixingSystematics
./lean/InfoGeometry/External/Auto/HestenesKreinColimitBridge.lean :: 22:namespace HestenesKreinColimitBridge
./lean/InfoGeometry/External/Auto/HolographicArchitect.lean :: 1:namespace HolographicArchitect
./lean/InfoGeometry/External/Auto/HolographicErlangenCompletion.lean :: 13:namespace HolographicErlangenCompletion
./lean/InfoGeometry/External/Auto/HolographicScaleExtinctions.lean :: 12:namespace HolographicScaleExtinctions
./lean/InfoGeometry/External/Auto/HoTTInfinityBridge.lean :: 11:namespace HoTTInfinityBridge
./lean/InfoGeometry/External/Auto/ImprovedLLMTheory.lean :: 6:namespace ImprovedLLMTheory
./lean/InfoGeometry/External/Auto/InformationGeometricCutoff.lean :: 17:namespace InformationGeometricCutoff
./lean/InfoGeometry/External/Auto/InstantonQCD.lean :: 5:namespace QCD_Instanton
./lean/InfoGeometry/External/Auto/IsospinSymmetryBreaking.lean :: 4:namespace IsospinSymmetryBreaking
./lean/InfoGeometry/External/Auto/JaynesLDDPGNSColimit.lean :: 18:namespace JaynesLDDPGNSColimit
./lean/InfoGeometry/External/Auto/JaynesLeanColimitBridge.lean :: 27:namespace JaynesLeanColimitBridge
./lean/InfoGeometry/External/Auto/J_duality_chain.lean :: 6:namespace LegacyJDualityChain
./lean/InfoGeometry/External/Auto/JordanBlock2.lean :: 5:namespace JordanBlock2
./lean/InfoGeometry/External/Auto/KanekoA67HighSpinMED.lean :: 5:namespace KanekoA67HighSpinMED
./lean/InfoGeometry/External/Auto/KaneMeleOrbifold.lean :: 1:namespace KaneMeleOrbifold
./lean/InfoGeometry/External/Auto/KANFourierMellinDirac.lean :: 20:namespace KANFourierMellinDirac
./lean/InfoGeometry/External/Auto/KasparovKreinDoubling.lean :: 12:namespace KasparovKrein
./lean/InfoGeometry/External/Auto/KleinBottleCobordism.lean :: 21:namespace UV_Cutoff
./lean/InfoGeometry/External/Auto/KleinBottle.lean :: 5:namespace KleinBottle
./lean/InfoGeometry/External/Auto/KleinGeometrySupergraded.lean :: 12:namespace KleinGeometrySupergraded
./lean/InfoGeometry/External/Auto/KleinGrapheneTunneling.lean :: 22:namespace KleinGrapheneTunneling
./lean/InfoGeometry/External/Auto/KoroteevZeitlin3DMirror.lean :: 13:namespace KoroteevZeitlin
./lean/InfoGeometry/External/Auto/krein_souriau.lean :: 4:namespace KreinSouriau
./lean/InfoGeometry/External/Auto/LanglandsGromovWitten.lean :: 6:namespace GeometricLanglandsLimit
./lean/InfoGeometry/External/Auto/LECM2022ElectroweakRadiiISB.lean :: 9:namespace LECM2022ElectroweakRadiiISB
./lean/InfoGeometry/External/Auto/LegendreFenchelSpectralGap.lean :: 18:namespace LegendreFenchelSpectralGap
./lean/InfoGeometry/External/Auto/LicataFinsterEMSpaces.lean :: 16:namespace LicataFinsterEMSpaces
./lean/InfoGeometry/External/Auto/LightConeTripotentMatrixBridge.lean :: 21:namespace LightConeTripotentMatrixBridge
./lean/InfoGeometry/External/Auto/LiuCollinsAffineInvariance.lean :: 12:namespace LiuCollins
./lean/InfoGeometry/External/Auto/LlewellynZr79MED.lean :: 5:namespace LlewellynZr79MED
./lean/InfoGeometry/External/Auto/LogDeterminantHomomorphism.lean :: 3:namespace LogDeterminantHomomorphism
./lean/InfoGeometry/External/Auto/LogDetSuperKahlerBarrier.lean :: 17:namespace LogDetSuperKahlerBarrier
./lean/InfoGeometry/External/Auto/MajoranaPrimonSpectralBridge.lean :: 18:namespace MajoranaPrimonSpectralBridge
./lean/InfoGeometry/External/Auto/master_equation.lean :: 64:namespace ConnesFlow
./lean/InfoGeometry/External/Automath/SpectralSquashCayleyDKT.lean :: 17:namespace SpectralSquashCayleyDKT
./lean/InfoGeometry/External/Auto/MaxCalFeynmanGaussBonnet.lean :: 4:namespace LegacyMaxCalFeynmanGaussBonnet
./lean/InfoGeometry/External/Auto/MellinWaveletScaleShiftDigest.lean :: 28:namespace MellinWaveletScaleShiftDigest
./lean/InfoGeometry/External/Auto/MetriplecticCausality.lean :: 13:namespace MetriplecticCausality
./lean/InfoGeometry/External/Auto/MinkowskiBiquaternion.lean :: 10:namespace MinkowskiBiquaternion
./lean/InfoGeometry/External/Auto/MITFInvariant.lean :: 22:namespace MITFInvariant
./lean/InfoGeometry/External/Auto/MITFOrientabilityFlow.lean :: 17:namespace MITF
./lean/InfoGeometry/External/Auto/MITFOrientability.lean :: 25:namespace MITF
./lean/InfoGeometry/External/Auto/MobiusWittenIndex.lean :: 15:namespace MobiusWittenIndex
./lean/InfoGeometry/External/Auto/MobiusWittenKleinIndex.lean :: 15:namespace MobiusWittenKleinIndex
./lean/InfoGeometry/External/Auto/ModularAutomorphismGroup.lean :: 19:namespace ModularAutomorphismGroup
./lean/InfoGeometry/External/Auto/ModularGlideCPT.lean :: 20:namespace ModularGlideCPT
./lean/InfoGeometry/External/Auto/ModularHolographicMetric.lean :: 18:namespace ModularHolographicMetric
./lean/InfoGeometry/External/Auto/ModularItakuraBiquaternion.lean :: 21:namespace ModularItakuraBiquaternion
./lean/InfoGeometry/External/Auto/ModularKreinReflectionColimit.lean :: 17:namespace ModularKreinReflectionColimit
./lean/InfoGeometry/External/Auto/ModularMonodromy.lean :: 21:namespace ModularMonodromy
./lean/InfoGeometry/External/Auto/MorandiWallpaperCohomology.lean :: 26:namespace MorandiWallpaperCohomology
./lean/InfoGeometry/External/Auto/NoncommutativeTilingAlgebra.lean :: 16:namespace NoncommutativeTilingAlgebra
./lean/InfoGeometry/External/Auto/NonInvertiblePenroseCategoricalSymmetry.lean :: 18:namespace NonInvertiblePenroseCategoricalSymmetry
./lean/InfoGeometry/External/Auto/NonIsoConf3DeRhamCohomologyFormula.lean :: 7:namespace NonIsoConf3DeRhamCohomologyFormula
./lean/InfoGeometry/External/Auto/NonIsoConf3DeRhamCooperad.lean :: 26:namespace NonIsoConf3DeRhamCooperad
./lean/InfoGeometry/External/Auto/NonIsoConf3DupontGysinModel.lean :: 22:namespace NonIsoConf3DupontGysinModel
./lean/InfoGeometry/External/Auto/NonIsoConf3LogCFTPotential.lean :: 14:namespace NonIsoConf3LogCFTPotential
./lean/InfoGeometry/External/Auto/NonIsoConf3LogWedgeObstruction.lean :: 18:namespace NonIsoConf3LogWedgeObstruction
./lean/InfoGeometry/External/Auto/NonIsoConf3OrlikSolomon.lean :: 19:namespace NonIsoConf3OrlikSolomon
./lean/InfoGeometry/External/Auto/NonIsoConf3QuadricCompactification.lean :: 22:namespace NonIsoConf3QuadricCompactification
./lean/InfoGeometry/External/Auto/NonIsoConf3QuadricD4Model.lean :: 19:namespace NonIsoConf3QuadricD4Model
./lean/InfoGeometry/External/Auto/NonIsoConf3QuadricD4PointCount.lean :: 22:namespace NonIsoConf3QuadricD4PointCount
./lean/InfoGeometry/External/Auto/NonIsoConf3RankDecision.lean :: 12:namespace NonIsoConf3RankDecision
./lean/InfoGeometry/External/Auto/NonOrientableBraid.lean :: 13:namespace NonOrientableBraid
./lean/InfoGeometry/External/Auto/NuclearChartSquareCalibration.lean :: 13:namespace NuclearChartSquareCalibration
./lean/InfoGeometry/External/Auto/NuclearPhononGenerators.lean :: 11:namespace NuclearPhononGenerators
./lean/InfoGeometry/External/Auto/NuclearPhononMetriplecticBridge.lean :: 10:namespace NuclearPhononMetriplecticBridge
./lean/InfoGeometry/External/Auto/NumberSystemColimits.lean :: 4:namespace NumberSystemLadder
./lean/InfoGeometry/External/Auto/OakuTakayamaDModuleDeRham.lean :: 26:namespace OakuTakayamaDModuleDeRham
./lean/InfoGeometry/External/Auto/OctonionMatrixEncodings.lean :: 21:namespace OctonionMatrixEncodings
./lean/InfoGeometry/External/Auto/Orientability.lean :: 9:namespace CoordinatePatch
./lean/InfoGeometry/External/Auto/OrlandiA67Proceedings.lean :: 5:namespace OrlandiA67Proceedings
./lean/InfoGeometry/External/Auto/PaperwallDiscreteSUSY.lean :: 13:namespace PaperwallDiscreteSUSY
./lean/InfoGeometry/External/Auto/PaperwallHolographicSUSY.lean :: 18:namespace PaperwallHolographicSUSY
./lean/InfoGeometry/External/Auto/PaperwallSUSY.lean :: 12:namespace PaperwallSUSY
./lean/InfoGeometry/External/Auto/PauliZornTrifactor.lean :: 21:namespace PauliZornTrifactor
./lean/InfoGeometry/External/Auto/PenroseArithmetic.lean :: 20:namespace PenroseArithmetic
./lean/InfoGeometry/External/Auto/PenroseCuntzKriegerHolography.lean :: 5:namespace PenroseCuntzKriegerHolography
./lean/InfoGeometry/External/Auto/PenroseKMSSpectralDimension.lean :: 18:namespace PenroseKMSSpectralDimension
./lean/InfoGeometry/External/Auto/PenroseSpinIncidenceTessellation.lean :: 14:namespace PenroseSpinIncidenceTessellation
./lean/InfoGeometry/External/Auto/penrose_wallpaper_colimit.lean :: 95:namespace PenrosePatch
./lean/InfoGeometry/External/Auto/PentagonPenroseWallpaperFractal.lean :: 19:namespace PentagonPenroseWallpaperFractal
./lean/InfoGeometry/External/Auto/PolynomialSymmetryOperators.lean :: 10:namespace PolynomialSymmetry
./lean/InfoGeometry/External/Auto/PrimaMateriaInformationGeometry.lean :: 9:namespace PrimaMateria
./lean/InfoGeometry/External/Auto/PrimeMellinSymplecticCAR.lean :: 8:namespace PrimeMellinSymplecticCAR
./lean/InfoGeometry/External/Auto/PrimonBosonFermionDuality.lean :: 24:namespace PrimonBosonFermionDuality
./lean/InfoGeometry/External/Auto/PrimonFockTraceBridge.lean :: 22:namespace PrimonFockTraceBridge
./lean/InfoGeometry/External/Auto/PrimonHilbertPolyaSeparation.lean :: 21:namespace PrimonHilbertPolyaSeparation
./lean/InfoGeometry/External/Auto/PrimonSuperThermodynamics.lean :: 8:namespace PrimonSuperThermo
./lean/InfoGeometry/External/Auto/primon_system.lean :: 17:namespace Primon
./lean/InfoGeometry/External/Auto/PRL124RuPairingSymmetry.lean :: 5:namespace PRL124RuPairingSymmetry
./lean/InfoGeometry/External/Auto/ProjectiveCrystalKappa.lean :: 18:namespace ProjectiveCrystalKappa
./lean/InfoGeometry/External/Auto/ProjectiveCrystalMackeyDecomposition.lean :: 22:namespace ProjectiveCrystalMackeyDecomposition
./lean/InfoGeometry/External/Auto/ProjectiveCrystalSymmetry.lean :: 22:namespace ProjectiveCrystalSymmetry
./lean/InfoGeometry/External/Auto/ProjectiveCrystalTopology.lean :: 12:namespace ProjectiveCrystal
./lean/InfoGeometry/External/Auto/ProjectiveCuntzToeplitzCARCCR.lean :: 16:namespace ProjectiveCuntzToeplitzCARCCR
./lean/InfoGeometry/External/Auto/ProjectiveGlideSuperchargeUnification.lean :: 16:namespace ProjectiveGlideSuperchargeUnification
./lean/InfoGeometry/External/Auto/ProjectiveKappaKleinMobius.lean :: 19:namespace ProjectiveKappaKleinMobius
./lean/InfoGeometry/External/Auto/ProjectiveMobiusMatrix.lean :: 22:namespace ProjectiveMobiusMatrix
./lean/InfoGeometry/External/Auto/ProjectivePenrosePGA.lean :: 16:namespace ProjectivePenrosePGA
./lean/InfoGeometry/External/Auto/ProjectiveSymmetryAlgebra.lean :: 14:namespace ProjectiveSymmetryAlgebra
./lean/InfoGeometry/External/Auto/ProjectiveWallpaperGaugePSA.lean :: 26:namespace ProjectiveWallpaperGaugePSA
./lean/InfoGeometry/External/Auto/PublishedThesisArchitecture.lean :: 16:namespace PublishedThesisArchitecture
./lean/InfoGeometry/External/Auto/Q8NuclearChirality.lean :: 13:namespace Q8NuclearChirality
./lean/InfoGeometry/External/Auto/QCDConfinementISDivergence.lean :: 4:namespace QCDThermodynamicConfinement
./lean/InfoGeometry/External/Auto/QDeformedSuperCuntz.lean :: 267:namespace QDeformedThreeLayerArchitecture
./lean/InfoGeometry/External/Auto/QRootOfUnityTruncation.lean :: 20:namespace QRootOfUnityTruncation
./lean/InfoGeometry/External/Auto/QuadraticConfiguration3.lean :: 27:namespace QuadraticConfiguration3
./lean/InfoGeometry/External/Auto/QuadricConf3BraidingCooperadBridge.lean :: 11:namespace QuadricConf3BraidingCooperadBridge
./lean/InfoGeometry/External/Auto/RamanScattering.lean :: 10:namespace RamanState
./lean/InfoGeometry/External/Auto/RegularizationCayleyPipeline.lean :: 16:namespace RegularizationCayleyPipeline
./lean/InfoGeometry/External/Auto/RelativeModularStateDikin.lean :: 22:namespace RelativeModularStateDikin
./lean/InfoGeometry/External/Auto/RelativisticBiquaternionKAN.lean :: 21:namespace RelativisticBiquaternionKAN
./lean/InfoGeometry/External/Auto/RescaledPhaseVolumeCanonical.lean :: 17:namespace RescaledPhaseVolumeCanonical
./lean/InfoGeometry/External/Auto/RGFixedPoint.lean :: 13:namespace RGFixedPoint
./lean/InfoGeometry/External/Auto/RiemannHypothesisIJIRT172568.lean :: 332:namespace RiemannHypothesisPaper
./lean/InfoGeometry/External/Auto/RiemannHypothesis.lean :: 18:namespace RiemannHypothesis
./lean/InfoGeometry/External/Auto/RiemannKleinDuality.lean :: 14:namespace RiemannKleinDuality
./lean/InfoGeometry/External/Auto/rigorous_proofs.lean :: 7:namespace LegacyRigorousProofs
./lean/InfoGeometry/External/Auto/RP3Octupole.lean :: 12:namespace RP3Topology
./lean/InfoGeometry/External/Auto/S3ColorSpinorDecomposition.lean :: 14:namespace S3ColorSpinorDecomposition
./lean/InfoGeometry/External/Auto/SarkarTwoLevelIsospinMixing.lean :: 5:namespace SarkarTwoLevelIsospinMixing
./lean/InfoGeometry/External/Auto/SarsBregmanDuality.lean :: 5:namespace SarsBregmanDuality
./lean/InfoGeometry/External/Auto/SarsCasimirSpring.lean :: 5:namespace SarsCasimirSpring
./lean/InfoGeometry/External/Auto/SarsChiralMassDilaton.lean :: 5:namespace SarsChiralMassDilaton
./lean/InfoGeometry/External/Auto/SarsGNSCompletion.lean :: 5:namespace SarsGNSCompletion
./lean/InfoGeometry/External/Auto/SarsGNSFronsdalJoseph.lean :: 5:namespace SarsGNSFronsdalJoseph
./lean/InfoGeometry/External/Auto/SarsGNSWeyl.lean :: 5:namespace SarsGNSWeyl
./lean/InfoGeometry/External/Auto/SarsItakuraModular.lean :: 5:namespace SarsItakuraModular
./lean/InfoGeometry/External/Auto/SarsMetriplecticOT.lean :: 5:namespace SarsMetriplecticOT
./lean/InfoGeometry/External/Auto/SarsModularWeakValue.lean :: 5:namespace SarsModularWeakValue
./lean/InfoGeometry/External/Auto/SarsRoadblock.lean :: 5:namespace SarsRoadblock
./lean/InfoGeometry/External/Auto/SarsSKMajoranaSYK.lean :: 5:namespace SarsSKMajoranaSYK
./lean/InfoGeometry/External/Auto/SarsSouriauDilaton.lean :: 5:namespace SarsSouriauDilaton
./lean/InfoGeometry/External/Auto/SarsSU5Cl55Supertrace.lean :: 5:namespace SarsSU5Cl55Supertrace
./lean/InfoGeometry/External/Auto/SarsWeylColimit.lean :: 5:namespace SarsWeylColimit
./lean/InfoGeometry/External/Auto/SheikhIsospinSymmetryBreaking.lean :: 5:namespace SheikhIsospinSymmetryBreaking
./lean/InfoGeometry/External/Auto/SmithHatIsingDuality.lean :: 16:namespace SmithHatIsingDuality
./lean/InfoGeometry/External/Auto/SolderingForms.lean :: 5:namespace SolderingForms
./lean/InfoGeometry/External/Auto/SolderingRoundTrip.lean :: 14:namespace Vec4
./lean/InfoGeometry/External/Auto/SolovievQPNMChiralCuntz.lean :: 33:namespace SolovievQPNMChiralCuntz
./lean/InfoGeometry/External/Auto/SouriauBiquaternionGaussian.lean :: 14:namespace SouriauBiquaternionGaussian
./lean/InfoGeometry/External/Auto/SouriauCasimirEntropyLeaves.lean :: 5:namespace SouriauCasimirEntropyLeaves
./lean/InfoGeometry/External/Auto/SouriauComplexTemperature.lean :: 3:namespace SouriauComplexTemperature
./lean/InfoGeometry/External/Auto/SouriauGaussian.lean :: 12:namespace SouriauGaussian
./lean/InfoGeometry/External/Auto/SouriauHestenesKrein.lean :: 5:namespace SouriauHestenesKrein
./lean/InfoGeometry/External/Auto/SouriauHestenesMobiusPole.lean :: 22:namespace SouriauHestenesMobiusPole
./lean/InfoGeometry/External/Auto/SouriauOperatorThermodynamics.lean :: 20:namespace SouriauOperatorThermodynamics
./lean/InfoGeometry/External/Auto/SouriauThermoColimit.lean :: 25:namespace SouriauThermoColimit
./lean/InfoGeometry/External/Auto/SpacetimeIsSpin.lean :: 17:namespace SpacetimeIsSpin
./lean/InfoGeometry/External/Auto/SpinorMonodromySteppingStone.lean :: 22:namespace SpinorMonodromySteppingStone
./lean/InfoGeometry/External/Auto/SpinorVectorDuality.lean :: 20:namespace V4
./lean/InfoGeometry/External/Auto/SplitOctonionMinkowski.lean :: 23:namespace SplitOctonionMinkowski
./lean/InfoGeometry/External/Auto/SplitOctonionNilpotent.lean :: 12:namespace SplitOctonionNilpotent
./lean/InfoGeometry/External/Auto/SplitOctonionZornKKS.lean :: 3:namespace SplitOctonionZornKKS
./lean/InfoGeometry/External/Auto/SquashingOperator.lean :: 12:namespace SquashingOperator
./lean/InfoGeometry/External/Auto/SU3LoopBraidDuality.lean :: 34:namespace SU3LoopBraidDuality
./lean/InfoGeometry/External/Auto/SUNLoopBraidCuntzBoundary.lean :: 22:namespace SUNLoopBraidCuntzBoundary
./lean/InfoGeometry/External/Auto/SuperBerezinianKlein.lean :: 18:namespace SuperBerezinianKlein
./lean/InfoGeometry/External/Auto/SuperchargeSquare.lean :: 16:namespace SuperchargeSquare
./lean/InfoGeometry/External/Auto/SuperPartitionBerezinian.lean :: 3:namespace SuperPartitionBerezinian
./lean/InfoGeometry/External/Auto/SymbolicFockLane.lean :: 25:namespace SymbolicFockLane
./lean/InfoGeometry/External/Auto/SymbolicLaneUHFBridge.lean :: 19:namespace SymbolicLaneUHFBridge
./lean/InfoGeometry/External/Auto/SymmetryReviewISB.lean :: 5:namespace SymmetryReviewISB
./lean/InfoGeometry/External/Auto/temp.lean :: 3:namespace ExternalTemp
./lean/InfoGeometry/External/Auto/test4.lean :: 5:namespace ExternalTest4
./lean/InfoGeometry/External/Auto/TestAF.lean :: 5:namespace ExternalTestAF
./lean/InfoGeometry/External/Auto/TestBraid.lean :: 6:namespace TestBraid
./lean/InfoGeometry/External/Auto/TestTL.lean :: 5:namespace TestTL
./lean/InfoGeometry/External/Auto/test_wrapper.lean :: 6:namespace TestWrapper
./lean/InfoGeometry/External/Auto/ThesisMaster.lean :: 22:namespace ThesisMaster
./lean/InfoGeometry/External/Auto/ThreeDMirrorSymmetry.lean :: 8:namespace ThreeDMirrorSymmetry
./lean/InfoGeometry/External/Auto/TKKCartanDecomposition.lean :: 11:namespace TKKCartanDecomposition
./lean/InfoGeometry/External/Auto/TKKCompileData.lean :: 16:namespace TKKCompileData
./lean/InfoGeometry/External/Auto/TKKQQBridge.lean :: 6:namespace TKKQQBridge
./lean/InfoGeometry/External/Auto/TKK_StandardModel.lean :: 16:namespace TKK_StandardModel
./lean/InfoGeometry/External/Auto/TomitaTakesakiRelativeEntropy.lean :: 3:namespace TomitaTakesakiRelativeEntropy
./lean/InfoGeometry/External/Auto/TPUAQLattice.lean :: 3:namespace AutonomousHypothesisEngine
./lean/InfoGeometry/External/Auto/TransformsAndScale.lean :: 20:namespace TransformsAndScale
./lean/InfoGeometry/External/Auto/TrifactorGeometry.lean :: 20:namespace TrifactorGeometry
./lean/InfoGeometry/External/Auto/TripotentCliffordColimit.lean :: 22:namespace TripotentCliffordColimit
./lean/InfoGeometry/External/Auto/TripotentPenroseHolography.lean :: 12:namespace TripotentPenrose
./lean/InfoGeometry/External/Auto/uhf_cantor_boundary.lean :: 10:namespace UhfCantorBoundary
./lean/InfoGeometry/External/Auto/UHFInductiveColimit.lean :: 22:namespace UHFInductiveColimit
./lean/InfoGeometry/External/Auto/uhf_ladder.lean :: 79:namespace MatrixTowerLevel
./lean/InfoGeometry/External/Auto/UnifiedKleinHolographicArchitecture.lean :: 15:namespace UnifiedKleinHolographicArchitecture
./lean/InfoGeometry/External/Auto/UthayakumaarMirrorKnockout.lean :: 5:namespace UthayakumaarMirrorKnockout
./lean/InfoGeometry/External/Auto/VacuumCohomology.lean :: 12:namespace VacuumCohomology
./lean/InfoGeometry/External/Auto/VacuumGroundstate.lean :: 7:namespace VacuumGroundstate
./lean/InfoGeometry/External/Auto/VacuumJonesKleinBirefringence.lean :: 17:namespace VacuumJonesKleinBirefringence
./lean/InfoGeometry/External/Auto/VarlamovKleinSpectral.lean :: 10:namespace VarlamovKleinSpectral
./lean/InfoGeometry/External/Auto/VerberckWallpaperFourier.lean :: 23:namespace VerberckWallpaperFourier
./lean/InfoGeometry/External/Auto/VertexAlgebraBraidingCocycle.lean :: 23:namespace VertexAlgebraBraidingCocycle
./lean/InfoGeometry/External/Auto/WallpaperBulkAnyonProjection.lean :: 20:namespace WallpaperBulkAnyonProjection
./lean/InfoGeometry/External/Auto/WallpaperClassification.lean :: 12:namespace WallpaperClassification
./lean/InfoGeometry/External/Auto/WallpaperCohomology.lean :: 29:namespace WallpaperCohomology
./lean/InfoGeometry/External/Auto/WallpaperFermionSuperconductingGap.lean :: 28:namespace WallpaperFermionSuperconductingGap
./lean/InfoGeometry/External/Auto/WallpaperIsometry.lean :: 9:namespace WallpaperIsometry
./lean/InfoGeometry/External/Auto/WallpaperMetamaterialDataset.lean :: 18:namespace WallpaperMetamaterialDataset
./lean/InfoGeometry/External/Auto/WallpaperSemidirectProduct.lean :: 13:namespace WallpaperSemidirectProduct
./lean/InfoGeometry/External/Auto/WarehamCGADilatorSL2.lean :: 5:namespace WarehamCGADilatorSL2
./lean/InfoGeometry/External/Auto/WarehamNullBasis55.lean :: 3:namespace WarehamNullBasis55
./lean/InfoGeometry/External/Auto/WeakIsospinSU2.lean :: 9:namespace WeakIsospinSU2
./lean/InfoGeometry/External/Auto/WeylGaugeItakuraSaito.lean :: 5:namespace WeylGaugeItakuraSaito
./lean/InfoGeometry/External/Auto/WignerMadelungKrein.lean :: 6:namespace PhaseSpace
./lean/InfoGeometry/External/Auto/WittenIndex.lean :: 4:namespace AnomalyCancellation
./lean/InfoGeometry/External/Auto/YanevaPd94PnSymmetry.lean :: 3:namespace YanevaPd94PnSymmetry
./lean/InfoGeometry/External/Auto/YangBaxterQuotientDescent.lean :: 14:namespace YangBaxterQuotientDescent
./lean/InfoGeometry/External/Auto/zeta_zeros_moebius_klein.lean :: 111:namespace MobiusStrip
./lean/InfoGeometry/External/Auto/ZornAssociatorSplitOctonion.lean :: 23:namespace ZornAssociatorSplitOctonion
./lean/InfoGeometry/External/Auto/ZornKleinGlideBridge.lean :: 21:namespace ZornKleinGlideBridge
./lean/InfoGeometry/External/Auto/ZornOPParavector.lean :: 24:namespace ZornOPParavector
./lean/InfoGeometry/External/Auto/ZornParavectorNullspace.lean :: 17:namespace ZornParavectorNullspace
./lean/InfoGeometry/External/Auto/ZornScalingFlowOrdered.lean :: 15:namespace ZornScalingFlowOrdered
./lean/InfoGeometry/External/Virasoro/AffineKacMoody.lean :: 26:namespace VirasoroProject
./lean/InfoGeometry/External/Virasoro/CentralChargeCalc.lean :: 45:namespace VirasoroProject
./lean/InfoGeometry/External/Virasoro/CentralExtension.lean :: 10:namespace VirasoroProject
./lean/InfoGeometry/External/Virasoro/ChiralProduct.lean :: 28:namespace VirasoroProject
./lean/InfoGeometry/External/Virasoro/Commutator.lean :: 21:namespace LinearMap
./lean/InfoGeometry/External/Virasoro/CyclicTripleSum.lean :: 42:namespace VirasoroProject
./lean/InfoGeometry/External/Virasoro/FiveGradedDecomposition.lean :: 24:namespace VirasoroProject
./lean/InfoGeometry/External/Virasoro/FockSpace.lean :: 61:namespace VirasoroProject
./lean/InfoGeometry/External/Virasoro/FockSpaceSugawara.lean :: 46:namespace VirasoroProject
./lean/InfoGeometry/External/Virasoro/HeisenbergAlgebra.lean :: 48:namespace VirasoroProject
./lean/InfoGeometry/External/Virasoro/HeisenbergFlip.lean :: 12:namespace VirasoroProject
./lean/InfoGeometry/External/Virasoro/HeisenbergModeFlip.lean :: 22:namespace VirasoroProject
./lean/InfoGeometry/External/Virasoro/IndexTri.lean :: 24:namespace VirasoroProject
./lean/InfoGeometry/External/Virasoro/IsCentralExtension.lean :: 38:namespace VirasoroProject
./lean/InfoGeometry/External/Virasoro/LieAlgebraRepresentationOfBasis.lean :: 26:namespace LieAlgebra
./lean/InfoGeometry/External/Virasoro/LieCohomologySmallDegree.lean :: 49:namespace VirasoroProject
./lean/InfoGeometry/External/Virasoro/LieVerma.lean :: 60:namespace VirasoroProject
./lean/InfoGeometry/External/Virasoro/SectionSES.lean :: 47:namespace MonoidHom
./lean/InfoGeometry/External/Virasoro/Sugawara.lean :: 49:namespace VirasoroProject
./lean/InfoGeometry/External/Virasoro/ToMathlib/LinearAlgebra/Basis/FinsumRepr.lean :: 51:namespace Module.Basis
./lean/InfoGeometry/External/Virasoro/VermaModule.lean :: 48:namespace VirasoroProject
./lean/InfoGeometry/External/Virasoro/VirasoroAlgebra.lean :: 47:namespace VirasoroProject
./lean/InfoGeometry/External/Virasoro/VirasoroCocycle.lean :: 40:namespace VirasoroProject
./lean/InfoGeometry/External/Virasoro/VirasoroVerma.lean :: 52:namespace VirasoroProject
./lean/InfoGeometry/External/Virasoro/WittAlgebraCohomology.lean :: 27:namespace VirasoroProject
./lean/InfoGeometry/External/Virasoro/WittAlgebra.lean :: 48:namespace VirasoroProject
./lean/InfoGeometry/FormalAgentLib/Layer1.lean :: 4:namespace FormalAgentLib
./lean/InfoGeometry/Foundations/AxiomaticDependencyGraph.lean :: 3:namespace Audit
./lean/InfoGeometry/GromovProbability.lean :: 20:namespace GromovProbability
./lean/InfoGeometry/Hestenes/SpacetimeAlgebra.lean :: 10:namespace HestenesSTA
./lean/InfoGeometry/HilbertTensorProduct.lean :: 8:namespace HilbertTensorProduct
./lean/InfoGeometry/HilbertTensorProduct/Phase2_HS2Ell2.lean :: 18:namespace HilbertTensorProduct
./lean/InfoGeometry/HilbertTensorProduct/Phase5_SpectralTheorem.lean :: 18:namespace HilbertTensorProduct.SpectralTheorem
./lean/InfoGeometry/JordanDecomposition.lean :: 23:namespace JordanDecomposition
./lean/InfoGeometry/Lie/MathlibBackportAdjointAction.lean :: 20:namespace LieAlgebra
./lean/InfoGeometry/Lie/MathlibBackportAEval.lean :: 8:namespace Module.End
./lean/InfoGeometry/Lie/MathlibBackportBasisLieEnd.lean :: 16:namespace Module.Basis
./lean/InfoGeometry/Lie/MathlibBackportCartanCriterionFoundations.lean :: 13:namespace Polynomial
./lean/InfoGeometry/Lie/MathlibBackportCartanCriterionFull.lean :: 57:namespace LieModule
./lean/InfoGeometry/Lie/MathlibBackportFreeBaseChange.lean :: 6:namespace LinearMap
./lean/InfoGeometry/Lie/MathlibBackportJordanChevalley.lean :: 13:namespace Module.End
./lean/InfoGeometry/MellinColimitTrifactor.lean :: 19:namespace MellinColimitTrifactor
./lean/InfoGeometry/Meta/FormalLogos.lean :: 45:namespace Meta.FormalLogos
./lean/InfoGeometry/Meta/ThermodynamicGEORegulation.lean :: 31:namespace Meta.ThermodynamicGEORegulation
./lean/InfoGeometry/Meta/TranscendentFunction.lean :: 49:namespace Meta.TranscendentFunction
./lean/InfoGeometry/Monster/MonsterMoonshineThermal.lean :: 21:namespace MonsterMoonshine
./lean/InfoGeometry/Optics/JonesCalculus.lean :: 16:namespace JonesCalulus
./lean/InfoGeometry/Optics/JonesCalculusSpinorLorentz.lean :: 7:namespace JonesCalculus
./lean/InfoGeometry/Peirce/PeirceLadderOperators.lean :: 22:namespace PeirceLadder
./lean/InfoGeometry/Physics/AlgebraicCuntzQuotient.lean :: 25:namespace AlgebraicCuntzQuotient
./lean/InfoGeometry/Physics/Algebra/SuperWiesbrockKreinBridge.lean :: 14:namespace SuperWiesbrock
./lean/InfoGeometry/Physics/AmplituhedronPenroseTransform.lean :: 13:namespace Amplituhedron
./lean/InfoGeometry/Physics/ChiralityPseudoscalarCuntz.lean :: 11:namespace ChiralityPseudoscalar
./lean/InfoGeometry/Physics/ChiralTensorRecoupling.lean :: 24:namespace ChiralTensorRecoupling
./lean/InfoGeometry/Physics/ChiralUncertaintyCaliber.lean :: 14:namespace ChiralUncertainty
./lean/InfoGeometry/Physics/PellisFineStructure.lean :: 19:namespace PellisFineStructure
./lean/InfoGeometry/Physics/SplitCliffordAlgebras.lean :: 38:namespace SplitClifford
./lean/InfoGeometry/Physics/TopologicalMTheoryGromovWitten.lean :: 11:namespace TopologicalMTheory
./lean/InfoGeometry/Physics/WeylSU3ColorSymmetry.lean :: 23:namespace WeylSU3ColorSymmetry
./lean/InfoGeometry/Probability/GromovConcentration.lean :: 20:namespace Gromov.Concentration
./lean/InfoGeometry/Probability/GromovFiniteCounting.lean :: 35:namespace Gromov.Probability
./lean/InfoGeometry/Probability/GromovProbability.lean :: 20:namespace GromovProbability
./lean/InfoGeometry/Probability/GromovProjectiveRatio.lean :: 23:namespace GromovSystem
./lean/InfoGeometry/Probability/GromovSystem.lean :: 27:namespace GromovSystem
./lean/InfoGeometry/Probability/SymmetricCounting.lean :: 21:namespace SymmetricCounting
./lean/InfoGeometry/Projective/QuantumTwistorDirac.lean :: 20:namespace QuantumTwistorDirac
./lean/InfoGeometry/Quantum/FibonacciFusionCategory.lean :: 44:namespace FibonacciFusion
./lean/InfoGeometry/Quiver/BetheAnsatzXXZ.lean :: 16:namespace KoroteevZeitlin.Bethe
./lean/InfoGeometry/Quiver/HbarOper.lean :: 19:namespace KoroteevZeitlin.Oper
./lean/InfoGeometry/Quiver/KoroteevZeitlinMirror.lean :: 31:namespace KoroteevZeitlin
./lean/InfoGeometry/Quiver/TKKHamiltonian.lean :: 8:namespace TKKHamiltonian
./lean/InfoGeometry/Quiver/XXZYangYang.lean :: 25:namespace KoroteevZeitlin.Bethe.XXZYangYang
./lean/InfoGeometry/Routing/BirkhoffVonNeumann.lean :: 13:namespace BirkhoffRouting
./lean/InfoGeometry/Sandbox/LefschetzFixedPoint.lean :: 19:namespace IsolatedFixedPoint
./lean/InfoGeometry/Sandbox/SpectralStabilitySandbox.lean :: 19:namespace BernsteinSato
./lean/InfoGeometry/Section10_11.lean :: 14:namespace Section10_11
./lean/InfoGeometry/Section10.lean :: 22:namespace Section10
./lean/InfoGeometry/Section11.lean :: 23:namespace Section11
./lean/InfoGeometry/Section12Formalized.lean :: 28:namespace Section12Formalized
./lean/InfoGeometry/Section12.lean :: 49:namespace Section12
./lean/InfoGeometry/Section13.lean :: 33:namespace Section13
./lean/InfoGeometry/Section15.lean :: 30:namespace Section15
./lean/InfoGeometry/Section16.lean :: 31:namespace Section16
./lean/InfoGeometry/Section17.lean :: 33:namespace Section17
./lean/InfoGeometry/Section18.lean :: 32:namespace Section18
./lean/InfoGeometry/Section19.lean :: 31:namespace Section19
./lean/InfoGeometry/Section20.lean :: 36:namespace Section20
./lean/InfoGeometry/Section21.lean :: 35:namespace Section21
./lean/InfoGeometry/Section22.lean :: 33:namespace Section22
./lean/InfoGeometry/Section24.lean :: 34:namespace Section24
./lean/InfoGeometry/Section25.lean :: 37:namespace Section25
./lean/InfoGeometry/Section26.lean :: 38:namespace Section26
./lean/InfoGeometry/Section2.lean :: 13:namespace Section2
./lean/InfoGeometry/Section3.lean :: 39:namespace Section3
./lean/InfoGeometry/Section4.lean :: 16:namespace Section4
./lean/InfoGeometry/Section5.lean :: 12:namespace Section5
./lean/InfoGeometry/Section6.lean :: 14:namespace Section6
./lean/InfoGeometry/Section7.lean :: 17:namespace Section7
./lean/InfoGeometry/Section8.lean :: 22:namespace Section8
./lean/InfoGeometry/Section9.lean :: 29:namespace Section9
./lean/InfoGeometry/TKK/TKKTest.lean :: 12:namespace D4TrialityPerm
./lean/InfoGeometry/Topology/D4SingularityDBrane.lean :: 32:namespace D4MatrixFactorization
./lean/InfoGeometry/Topology/DBraneMatrixFactorization.lean :: 26:namespace MatrixFactorization
./lean/InfoGeometry/Topology/GeneralizedCircleMobius.lean :: 20:namespace GeneralizedCircle
./lean/InfoGeometry/Topology/PainleveIsomonodromy.lean :: 35:namespace PainleveIsomonodromy
./lean/InfoGeometry/TrifactorDecomposition.lean :: 10:namespace TrifactorDecomposition
./lean/InfoGeometry/TrifactorGeometry.lean :: 13:namespace TrifactorGeometry
./lean/InfoGeometry/TrifactorProjectors.lean :: 15:namespace TrifactorProjectors
./lean/InfoGeometry/TwistorSmoothness.lean :: 21:namespace TwistorSmoothness
./lean/InfoGeometry/UnifiedMatrixBasis.lean :: 14:namespace UnifiedMatrixBasis

=== Namespace prefix histogram (first namespace line per file) ===
   8194 InfoGeometry
     74 CStarStateColimit
     30 Bridge
     24 SplitOctonion
     22 VirasoroProject
     22 Automath
     19 ZornCell
     13 GradedExactCouple
     12 CertifiedInverseKernel
     11 ZornMatrix
     11 SymmetricLieAlgebra
     10 Audit
      9 Derivation
      9 ConformalInference
      8 TwoPeriodicComplex
      8 PhaseLinear
      8 NoncommutativeGeometry
      8 GromovWittenErlangen
      6 ThreeLevelFiniteGibbs
      6 Tensor
      6 RawCARModeCompletion
      6 Module
      6 ExactCouple
      6 CertifiedConformalInference
      6 Canonical
      5 ZornProjectiveDatum
      5 Zorn
      5 RealSplitKreinKasparovCycle
      5 LinearMap
      5 LieTwoCocycle

[audit] Done.
```

## Orphaned Lean file audit

```text
[orphaned-check] Orphaned top-level Lean file in lean/: CheckBasis.lean
```

## Quarantine Boundary Audit

```text
Forbidden quarantined import: InfoGeometry.Canonical.RedLine in lean/InfoGeometry.lean:43
Quarantine import boundary check failed.
```

## Exact Constructivity Audit

```text
