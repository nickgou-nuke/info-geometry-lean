# Theory Audit Report

Generated: 2026-07-24 05:50:04Z

## Build toolchain status
- lake: available (/home/goutev/.elan/bin/lake)
```bash
Lake version 5.0.0-src+7e01a1b (Lean version 4.28.0)
```

## Placeholder proof debt (sorry/admit)

```text
lean/InfoGeometry/SelfReference/Shadow.lean:64:| ShadowKind.sorryDebt => "explicit sorry in proof body"
lean/InfoGeometry/Probability/HomologicalProbability.lean:823:Type III von Neumann factors admit no finite normal tracial state.
lean/InfoGeometry/Application/OperatorFreudenthalBoundary.lean:167:  /-- Boundary states admit Drazin surgery. -/
lean/InfoGeometry/Automorphic/HeckePurification.lean:82:  `Prop`/`sorry` placeholder with a concrete theorem-shaped obligation.
lean/InfoGeometry/Lie/Pin55KreinConformalBridge.lean:28:* Remaining `sorry` debt, with exact blocker names:
lean/InfoGeometry/Lie/Pin55KreinConformalBridge.lean:259:  sorry
lean/InfoGeometry/Eval/SorryFillerTest.lean:6:This file contains controlled `sorry` placeholders used as evaluation targets
lean/InfoGeometry/Eval/SorryFillerTest.lean:7:for the GEPA skill evolution loop. Each theorem has a `sorry` that needs to
lean/InfoGeometry/Lint/NonTriviality.lean:27:* transitive axiom audit using `Lean.collectAxioms`, with explicit `sorry` treated as honest closure debt when configured;
lean/InfoGeometry/Lint/NonTriviality.lean:57:/-- Permit explicit `sorry` as honest, visible closure debt. -/
lean/InfoGeometry/Lint/Pauli.lean:11:/-- Option to control the Pauli sorry linter. -/
lean/InfoGeometry/Lint/Pauli.lean:12:register_option linter.pauli.sorry : Bool := {
lean/InfoGeometry/Lint/Pauli.lean:51:      linter.pauli.sorry.get (← getOptions) ||
lean/InfoGeometry/Lint/Pauli.lean:92:              if linter.pauli.sorry.get (← getOptions) then
lean/InfoGeometry/Lint/Pauli.lean:100:                  logError m!"[Pauli/Axiom-Surface Seal] {declName} depends on nonstandard `admitAx`; use explicit `sorry` instead of a disguised placeholder."
lean/InfoGeometry/Analysis/AsanoRuelleBasicBranches.lean:16:No `sorry`.
lean/InfoGeometry/Analysis/LaplaceUniqueness.lean:302:If two Laplace data agree on the same Bromwich contour and both admit the
lean/InfoGeometry/OperatorAlgebra/SplitQuaternionSL2Isomorphism.lean:20:All proofs are native Lean 4 derivations checked by the kernel with zero remaining sorry debt.
lean/InfoGeometry/AsanoRuelle/MobiusInversion.lean:9:No placeholders. No `sorry`.
lean/InfoGeometry/OperatorAlgebra/SplitOctonionLoxodromic.lean:18:All proofs are native Lean 4 derivations checked by the kernel with zero remaining sorry debt.
lean/InfoGeometry/AsanoRuelle/AsanoRuelleCounterexample.lean:12:No wrappers. No `sorry`.
lean/InfoGeometry/OperatorAlgebra/SplitOctonionPseudoReal.lean:18:No `sorry`/`axiom`/`admit`/certificate scaffolding is used.
lean/InfoGeometry/OperatorAlgebra/TripotentFactorization.lean:11:All proofs are native Lean 4 derivations checked by the kernel with zero sorry debt.
lean/InfoGeometry/OperatorAlgebra/ChiralCliffordSplit.lean:17:All proofs are native, formal Lean 4 derivations checked by the kernel with zero sorry debt.
lean/InfoGeometry/OperatorAlgebra/TripotentMatrix2x2.lean:15:All proofs are native Lean 4 derivations checked by the kernel with zero remaining sorry debt.
lean/InfoGeometry/OperatorAlgebra/WittenMöbiusBraidBridge.lean:18:All proofs are native Lean 4 derivations checked by the kernel with zero remaining sorry debt.
lean/InfoGeometry/Meta/OwnerTarget.lean:43:  A `sorry` in an owner-target proof is machine-visible closure debt.
lean/InfoGeometry/Meta/ThermodynamicGEORegulation.lean:37:  fitness : ℝ          -- between 0 and 1 (1 = compiles, 0 = sorry)
lean/InfoGeometry/Meta/HonestyPolicy.lean:15:- if it does not exist yet, expose the gap explicitly as `sorry` or an
lean/InfoGeometry/Meta/HonestyPolicy.lean:43:  /-- Explicit `sorry` is acceptable only as visible debt. -/
lean/InfoGeometry/Meta/HonestyPolicy.lean:47:  /-- Banner text must not claim certified readback when `sorry` remains. -/
lean/InfoGeometry/Meta/HonestyPolicy.lean:59:    "If a Mathlib-rooted derivation chain is missing, expose the gap explicitly as sorry or an explicit zero-datum. Do not hide debt behind fake witnesses, empty shells, or misleading certification banners."
lean/InfoGeometry/Clifford/FanoOctonionParavector.lean:12:All proofs are native and closed without sorry.
lean/InfoGeometry/Meta/ShadowLedger.lean:6:The shadow ledger tracks every `:= by sorry` declaration in the repository.
lean/InfoGeometry/Meta/ShadowLedger.lean:30:Every `:= by sorry` is a seed for the next evolution cycle.
lean/InfoGeometry/External/Auto/RegularizationCayleyPipeline.lean:10:work behind a `sorry`.  The finite SymPy witness in
lean/InfoGeometry/Meta/ClosureAttribute.lean:11:anchored to the DAG, and free of `sorry` or `admit`.
lean/InfoGeometry/Meta/SocketTarget.lean:12:normal `sorry` detection because the law itself is a parameter.
lean/InfoGeometry/Meta/SocketTarget.lean:29:   closure debt — the architectural equivalent of a typed `sorry`.
lean/InfoGeometry/Meta/SocketTarget.lean:49:not check for `sorry` — sockets are *expected* to carry opaque laws.
lean/InfoGeometry/Meta/Admission.lean:141:      mkAdmissionReason syntheticDecl "trust.sorry" "error"
lean/InfoGeometry/Meta/StrictDef.lean:18:  , ``Lean.Parser.Term.«sorry»
lean/InfoGeometry/Meta/StrictDef.lean:31:      "strict {declKind} `{declName}` uses forbidden term syntax (`by`, `sorry`, or `unsafe`) in its type."
lean/InfoGeometry/Meta/StrictDef.lean:34:      "strict {declKind} `{declName}` uses forbidden term syntax (`by`, `sorry`, or `unsafe`) in its value."
lean/InfoGeometry/Meta/StrictDef.lean:291:It accepts only ordinary `def` syntax and rejects tactic blocks, `sorry`, and
lean/InfoGeometry/Automath.lean:12:`by sorry` marking the gap between hypothesis and proof.
lean/InfoGeometry/Automath.lean:29:- Marked with `by sorry` as an honest gap (NOT `by trivial`)
lean/InfoGeometry/Algebra/NilpotentNonunit.lean:11:No wrappers. No `sorry`.
lean/InfoGeometry/Topology/MobiusDeRhamMonodromy.lean:22:## Verified theorems (no sorry)
lean/InfoGeometry/Clifford/ConformalReflection55.lean:36:These are **native Lean proofs** — no axioms, sorry, or external certificates.
lean/InfoGeometry/Tooling/VacuityCritic.lean:24:    field.value != "sorry" && field.value != "admit"
lean/InfoGeometry/External/Auto/BlackHoleHolography.lean:9:is proved without axioms or `sorry`.
lean/InfoGeometry/Signal/QuaternionPhase.lean:14:No assumptions, axioms, or `sorry`/`admit` scaffolding are used.
lean/InfoGeometry/Algebra/Zorn/ConcreteComposition.lean:15:No wrappers. No `sorry`.
lean/InfoGeometry/Topology/CliffordMobiusDeRhamMonodromy.lean:17:## Verified theorems (no sorry)
lean/InfoGeometry/Automath/Generated/cuntz_fibonacci_resolvent.lean:14:  sorry
lean/InfoGeometry/Algebra/AssociativityObstruction.lean:31:* therefore a genuinely nonassociative algebra cannot admit such a
lean/InfoGeometry/Automath/Generated/hyp_2_fibonacci_functional_calculus.lean:14:  sorry
lean/InfoGeometry/Algebra/CuntzRecursiveFermionSystem.lean:219:/-! ## Wedge Actions (sorry-free) -/
lean/InfoGeometry/Automath/Generated/hyp_5_k_theory.lean:14:  sorry
lean/InfoGeometry/Algebra/Zorn/ConcreteBarrier.lean:18:No `sorry`.
lean/InfoGeometry/Algebra/ZeckendorfBijection.lean:15:NO `sorry`, NO `axiom`, NO `admit`. Every line is kernel-checked.
lean/InfoGeometry/Automath/Generated/cuntz_yang_baxter.lean:14:  sorry
lean/InfoGeometry/Algebra/Zorn/Concrete.lean:9:No wrappers. No abstract datum. No `sorry`.
lean/InfoGeometry/Automath/Generated/hyp_3_operator_roots.lean:14:  sorry
lean/InfoGeometry/Automath/Generated/hyp_4_braid_image.lean:10:  sorry
lean/InfoGeometry/Automath/Generated/hyp_1_spectral_rigidity.lean:14:  sorry
lean/InfoGeometry/Topology/MobiusNonParabolicRecovered.lean:15:/-- On the Riemann sphere, every two distinct points admit a third distinct point. -/
lean/InfoGeometry/Automath/Generated/cuntz_shift_commutativity.lean:14:  sorry
lean/InfoGeometry/Algebra/HypercomplexTriadMatrix.lean:18:No `sorry`.
lean/InfoGeometry/Algebra/GoldenMeanShift.lean:22:NO `sorry`, NO `axiom`, NO `admit`. Every line is kernel-checked.
lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean:2070:Kept as a `Prop` (not a `theorem ... := by sorry`) because this module does not
lean/InfoGeometry/Algebra/NoFaithfulAssociativeModel.lean:17:No wrappers. No structures. No `sorry`.
lean/InfoGeometry/Arithmetic/GenuineBounds.lean:81:  · sorry
lean/InfoGeometry/Arithmetic/GenuineBounds.lean:151:  sorry
lean/InfoGeometry/Algebra/CuntzTraceSocketConjugation.lean:17:The remaining lemmas and operator-level lift are left as `sorry` markers
lean/InfoGeometry/Algebra/CuntzTraceSocketConjugation.lean:74:explicit `sorry` placeholders so the missing proofs are visible.
lean/InfoGeometry/Algebra/CuntzTraceSocketConjugation.lean:118:  sorry
lean/InfoGeometry/Algebra/CuntzTraceSocketConjugation.lean:126:  sorry
lean/InfoGeometry/Algebra/CuntzTraceSocketConjugation.lean:136:      = invPairingSocket socket S T := by sorry
lean/InfoGeometry/Algebra/CuntzTraceSocketConjugation.lean:139:      = logPotentialSocket socket S := by sorry
lean/InfoGeometry/Algebra/CuntzTraceSocketConjugation.lean:142:      = logPotentialSocket socket T := by sorry
lean/InfoGeometry/Algebra/CuntzTraceSocketConjugation.lean:162:  sorry
lean/InfoGeometry/Algebra/CuntzTraceSocketConjugation.lean:170:  sorry
lean/InfoGeometry/Arithmetic/LPrimitive.lean:153:-- with actual native Lean theorems. The `sorry` forms are completely eliminated!
lean/InfoGeometry/Canonical/TomitaFisherMetric.lean:17:No wrappers. No `sorry`.
lean/InfoGeometry/Arithmetic/SelfConcordantZetaBarrierProofs.lean:6:No sockets. No certificates. No axioms. No `sorry`.
lean/InfoGeometry/Arithmetic/ZetaDihedral.lean:15:No sockets. No certificates. No axioms. No `sorry`.
lean/InfoGeometry/Canonical/SO3RotationFenchelWitness.lean:14:No wrappers. No `sorry`.
lean/InfoGeometry/Arithmetic/PolyaHilbertDiracHodgeCantorBridge.lean:20:Plus the internal proof: `SouriauDiracHodgeCoupling` (659 lines, 32 thm, 0 sorry).
lean/InfoGeometry/Canonical/LieOrbitInfinitesimal.lean:13:No wrappers. No `sorry`.
lean/InfoGeometry/Projective/SplitOctonions/SplitOctonionsLegendre.lean:21:No wrappers. No `sorry`.
lean/InfoGeometry/Projective/SplitOctonions/SplitOctonionsColorStabilizer.lean:14:No wrappers. No `sorry`.
lean/InfoGeometry/Projective/SplitOctonions/ProjectivePolarInvariant.lean:21:No `sorry`.
lean/InfoGeometry/Projective/SplitOctonions/BektasMatrix.lean:14:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/ModularTensorInduction.lean:15:No wrappers. No `sorry`.
lean/InfoGeometry/Projective/SplitOctonions/ProjectivePolarFiberTransport.lean:22:No `sorry`.
lean/InfoGeometry/Projective/Quadrics/AffineSlices.lean:23:No `sorry`.
lean/InfoGeometry/Projective/SplitOctonions/ProjectivePolarFiber.lean:19:No `sorry`.
lean/InfoGeometry/Projective/KleinQuadric.lean:23:No `sorry`.
lean/InfoGeometry/Canonical/LieOrbitSymmetryChart2x2.lean:9:No wrappers. No `sorry`.
lean/InfoGeometry/Projective/SplitOctonions.lean:16:No `sorry`, no `True` placeholders, no fake Freudenthal determinant.
lean/InfoGeometry/Projective/KleinQuadricIncidence.lean:16:No wrappers. No `sorry`.
lean/InfoGeometry/Projective/KleinQuadricPlucker.lean:16:No wrappers. No `sorry`.
lean/InfoGeometry/Projective/KleinCrossRatioInvariant.lean:16:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/LeeYangAsanoMobiusNative.lean:25:No `sorry`.
lean/InfoGeometry/Canonical/CognitiveShadow.lean:48:      triggerTerms := #["sorry", "proof debt", "hole"]
lean/InfoGeometry/Canonical/MajoranaKitaevSpinorBridge.lean:18:It does not depend on the sorry-equivalent modular spinor layer.
lean/InfoGeometry/Canonical/AsanoRuellePoleExclusion.lean:9:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/SplitCliffordVacuumExpectation.lean:15:No placeholders. No `sorry`.
lean/InfoGeometry/Canonical/LeeYangAsanoNativeCore.lean:17:No `sorry`.
lean/InfoGeometry/Canonical/TomitaBregmanDuality.lean:20:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/AsanoRuelleTopologicalEndpoint.lean:19:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/SplitCliffordChiralProjection.lean:17:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/CartanSuperbracketClosure.lean:29:No `sorry`.
lean/InfoGeometry/Canonical/AsanoRuelleCounterexample.lean:15:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/ModularSL2R.lean:11:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/CantorHaarDiracSea.lean:18:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/AlgebraicDerivations.lean:13:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/SplitCliffordFiniteCurrentObstruction.lean:21:No `sorry`.
lean/InfoGeometry/Canonical/GrandCanonicalSouriau.lean:18:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/TopologicalGroupIsoExpLog.lean:13:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/RelativeDeterminantScatteringSocket.lean:10:unsupported claims are exposed as explicit `sorry` debt, not hidden as arbitrary
lean/InfoGeometry/Canonical/DrazinAnomalousProjector.lean:16:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/BayesianConformalCompression.lean:16:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/SplitCliffordJordanWignerTwoModeCurrent.lean:13:No `sorry`.
lean/InfoGeometry/Canonical/DimensionAgnosticModularKLDivergence.lean:7:remaining fully constructive (no `sorry`).
lean/InfoGeometry/Canonical/RindlerWeylDecomposition.lean:21:No placeholders. No `sorry`.
lean/InfoGeometry/Canonical/ChiralKKTIsolation.lean:11:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/FenchelExpLogCore.lean:14:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/SplitCliffordTwoModeWick.lean:16:No placeholders. No `sorry`.
lean/InfoGeometry/Canonical/DepthLogScaleInvariant.lean:21:No `sorry`.
lean/InfoGeometry/Canonical/OperatorPenroseUnification.lean:118:/-- Junction 5: spinor-modular identification without sorry-equivalent layer. -/
lean/InfoGeometry/Canonical/GaugeGroups.lean:14:Dead declarations (`SU2N`, `block_embedding_*`) removed — sorry-equivalent
lean/InfoGeometry/Canonical/GaugeGroups.lean:15:with zero external consumers. See `reports/dag/sorry-equivalence.md`.
lean/InfoGeometry/Canonical/GeneralizedOperatorChiral.lean:9:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/LieOrbitAdjointInvariants.lean:13:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/LieFenchelQuadratic.lean:15:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/KreinMajoranaZeroModeBlock.lean:11:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/ModularLorentzBoost.lean:9:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/PrimeLeeYangLargeDeviation.lean:23:`sorry` debt, not as arbitrary `Prop` fields.
lean/InfoGeometry/Canonical/SplitCliffordTwoModeTrace.lean:11:No placeholders. No `sorry`.
lean/InfoGeometry/Canonical/LeeYangAsanoDigest.lean:858:`Analysis.AsanoContractionNative` (no `sorry`).
lean/InfoGeometry/Canonical/LeeYangAsanoDigest.lean:1039:`sorry`.
lean/InfoGeometry/Canonical/SouriauInfinitesimalInvariance.lean:8:No wrappers. No `sorry`.
lean/InfoGeometry/Canonical/CliffordWaveletAnalyticBridge.lean:17:No `sorry`.
lean/InfoGeometry/Canonical/QuaternionCoaxialOrbit.lean:10:No wrappers. No `sorry`.
```

- Total placeholder occurrences in canonical tree: 147

## Axiom declarations

```text
```
- Total explicit axiom declarations: 0

## Namespace audit

```text
[audit] Project namespace: InfoGeometry
[audit] Scanning root:       ./lean/InfoGeometry

[audit] Files with namespace InfoGeometry*: 3873
[audit] Files missing namespace InfoGeometry*: 801

=== Missing namespace InfoGeometry ===
./lean/InfoGeometry/Algebra/BerezinianPfaffianBott.lean
./lean/InfoGeometry/Algebra/Cl11Fermions.lean
./lean/InfoGeometry/Algebra/CuntzFibonacciBraidInclusion.lean
./lean/InfoGeometry/Algebra/Det2.lean
./lean/InfoGeometry/Algebra/FibonacciParafermion.lean
./lean/InfoGeometry/Algebra/Grothendieck.lean
./lean/InfoGeometry/Algebra/HodgeDiracDelta.lean
./lean/InfoGeometry/Algebra/HodgeKreinTriFacet.lean
./lean/InfoGeometry/Algebra/Hypothesis1.lean
./lean/InfoGeometry/Algebra/IdeleCuntzSymmetry.lean
./lean/InfoGeometry/Algebra/IdempotentProjector.lean
./lean/InfoGeometry/Algebra/K0FibonacciRing.lean
./lean/InfoGeometry/Algebra/KreinPosNegDecomposition.lean
./lean/InfoGeometry/Algebra/SuperTraceBerezinian.lean
./lean/InfoGeometry/Algebra/TriFacetMatrixRealization.lean
./lean/InfoGeometry/Algebra/TriFacetSpectralPowers.lean
./lean/InfoGeometry/Algebra/TripotentClSUSYBridge.lean
./lean/InfoGeometry/Algebra/UnitizationNonAssoc.lean
./lean/InfoGeometry/Algebra/VerlindeSMatrix.lean
./lean/InfoGeometry/Algebra/Zorn/_CheckNames.lean
./lean/InfoGeometry/All.lean
./lean/InfoGeometry/Analysis/All.lean
./lean/InfoGeometry/Arithmetic/DirichletModeFactorization.lean
./lean/InfoGeometry/Arithmetic.lean
./lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbertSocket.lean
./lean/InfoGeometry/Arithmetic/PrimeSpinorWittenIndex.lean
./lean/InfoGeometry/Arithmetic/ProjectiveRelativeEntropy.lean
./lean/InfoGeometry/Arithmetic/SandboxPrimeParafermionRecurrenceTest.lean
./lean/InfoGeometry/Arithmetic/SandboxPrimeThermodynamicStageTest.lean
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
./lean/InfoGeometry/Canonical/AubertPlymen.lean
./lean/InfoGeometry/Canonical/AutoGeneratedKrein.lean
./lean/InfoGeometry/Canonical/AutomorphicSugawaraCalibration.lean
./lean/InfoGeometry/Canonical/BerryHolonomy.lean
./lean/InfoGeometry/Canonical/BiquaternionKANnilpotent.lean
./lean/InfoGeometry/Canonical/BiquaternionLaplaceTripotent.lean
./lean/InfoGeometry/Canonical/BiquaternionNegativeRootsLog.lean
./lean/InfoGeometry/Canonical/BostConnesKTheoryIntegration.lean
./lean/InfoGeometry/Canonical/CanonicalZornCliffordIsomorphism.lean
./lean/InfoGeometry/Canonical/CanonicalZornCliffordRepresentation.lean
./lean/InfoGeometry/Canonical/CanonicalZornCompositionFiveGradeBridge.lean
./lean/InfoGeometry/Canonical/CanonicalZornCompositionTriality.lean
./lean/InfoGeometry/Canonical/CanonicalZornFiveGradedClosure.lean
./lean/InfoGeometry/Canonical/CanonicalZornIntegralSpinRepresentation.lean
./lean/InfoGeometry/Canonical/CanonicalZornIntegralSpinSubgroup.lean
./lean/InfoGeometry/Canonical/CanonicalZornIntegralSpinTrialityClosure.lean
./lean/InfoGeometry/Canonical/CanonicalZornIntegralTrialityEquivariance.lean
./lean/InfoGeometry/Canonical/CanonicalZornOuterTrialityGroup.lean
./lean/InfoGeometry/Canonical/CanonicalZornProjectiveCore.lean
./lean/InfoGeometry/Canonical/CanonicalZornProjectiveTKKBridge.lean
./lean/InfoGeometry/Canonical/CanonicalZornRealComplexSpinBaseChange.lean
./lean/InfoGeometry/Canonical/CanonicalZornRealSpin44.lean
./lean/InfoGeometry/Canonical/CanonicalZornRealSpinTrialityClosure.lean
./lean/InfoGeometry/Canonical/CanonicalZornSpinChirality.lean
./lean/InfoGeometry/Canonical/CanonicalZornSpinRelatedFiber.lean
./lean/InfoGeometry/Canonical/CanonicalZornUnifiedClosure.lean
./lean/InfoGeometry/Canonical/CantorCoadjointHamiltonianFlowBridge.lean
./lean/InfoGeometry/Canonical/CausalFunctor.lean
./lean/InfoGeometry/Canonical/ChiralAnomalyCantor.lean
./lean/InfoGeometry/Canonical/CliffordCantorModeHierarchy.lean
./lean/InfoGeometry/Canonical/CliffordInfiniteSplitAlgebra.lean
./lean/InfoGeometry/Canonical/ConcreteCuntzKCommutation.lean
./lean/InfoGeometry/Canonical/ConcreteSuperVirasoroColimitReadback.lean
./lean/InfoGeometry/Canonical/ConformalEngine.lean
./lean/InfoGeometry/Canonical/ConformalProjectiveClosure.lean
./lean/InfoGeometry/Canonical/ConformalSubalgebraDebt.lean
./lean/InfoGeometry/Canonical/ConnesRadonNikodymCocycle.lean
./lean/InfoGeometry/Canonical/CyclicCocycleCantor.lean
./lean/InfoGeometry/Canonical/FibonacciAnyonSimilarity.lean
./lean/InfoGeometry/Canonical/FormalVerificationPacket.lean
./lean/InfoGeometry/Canonical/HessianGeometry.lean
./lean/InfoGeometry/Canonical/InductiveOperatorTaylorClosure.lean
./lean/InfoGeometry/Canonical/IntegralZornBilinearComposition.lean
./lean/InfoGeometry/Canonical/IntegralZornCompositionAlgebra.lean
./lean/InfoGeometry/Canonical/IntegralZornII44Bridge.lean
./lean/InfoGeometry/Canonical/JaynesFormalism.lean
./lean/InfoGeometry/Canonical/JordanWignerCelikKocakBridgeNDepth_proposal.lean
./lean/InfoGeometry/Canonical/K0Functor.lean
./lean/InfoGeometry/Canonical/KleinBottleSewing.lean
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
./lean/InfoGeometry/Canonical/ModularEvolution.lean
./lean/InfoGeometry/Canonical/ModularTomitaGeometry.lean
./lean/InfoGeometry/Canonical/NormalConeInductive.lean
./lean/InfoGeometry/Canonical/Positivity.lean
./lean/InfoGeometry/Canonical/PrimeCocycleCoefficients.lean
./lean/InfoGeometry/Canonical/ProjectiveAffineConformalClosure55.lean
./lean/InfoGeometry/Canonical/Sandbox/QuantumGrassmannian.lean
./lean/InfoGeometry/Canonical/SelfDualWeylKleinBridge.lean
./lean/InfoGeometry/Canonical/SingularityCausalCoupling.lean
./lean/InfoGeometry/Canonical/S_left_K_commutation.lean
./lean/InfoGeometry/Canonical/SplitQuaternionConcrete.lean
./lean/InfoGeometry/Canonical/StoneCantorMathlibScratch.lean
./lean/InfoGeometry/Canonical/TensorTowerColimit.lean
./lean/InfoGeometry/Canonical/TFDCartanAudit.lean
./lean/InfoGeometry/Canonical/TFDNilpotentCartanAudit.lean
./lean/InfoGeometry/Canonical/TFDNilpotentCartanAudit_user.lean
./lean/InfoGeometry/Canonical/TKKJordanPairData.lean
./lean/InfoGeometry/Canonical/WeylCantorCrystal.lean
./lean/InfoGeometry/Canonical/WeylCantorSynthesis.lean
./lean/InfoGeometry/Canonical/WeylIntegrationFixedPoint.lean
./lean/InfoGeometry/Canonical/ZornCellComposition.lean
./lean/InfoGeometry/Canonical/ZornCore.lean
./lean/InfoGeometry/Canonical/ZornOuterTrialityGroup.lean
./lean/InfoGeometry/Canonical/ZornTrialityTKKBridge.lean
./lean/InfoGeometry/Carrier/All.lean
./lean/InfoGeometry/Carrier/CliffordAction.lean
./lean/InfoGeometry/Categorical/All.lean
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
./lean/InfoGeometry/Categorical/GromovPositiveCone.lean
./lean/InfoGeometry/Categorical/InfinityTopos.lean
./lean/InfoGeometry/Categorical/MobiusGeometry.lean
./lean/InfoGeometry/Categorical/ZornBraidColimitBCFW.lean
./lean/InfoGeometry/Categorical/ZornBraidColimitKMS.lean
./lean/InfoGeometry/Causal/Algebra.lean
./lean/InfoGeometry/Clifford/CliffordInjectivity.lean
./lean/InfoGeometry/Clifford/Hestenes1975.lean
./lean/InfoGeometry/Clifford/QuadraticPolarBridge.lean
./lean/InfoGeometry/Clifford/SpinorRep_REAL.lean
./lean/InfoGeometry/Compatibility/All.lean
./lean/InfoGeometry/CoverageClosure.lean
./lean/InfoGeometry/DeterminantTrifactor.lean
./lean/InfoGeometry/E8/E8TrialityThermalProtection.lean
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
./lean/InfoGeometry/External/Auto/CognitiveVacuum.lean
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
./lean/InfoGeometry/External/Auto/CuntzEndomorphism.lean
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
./lean/InfoGeometry/External/Auto/TitsBruhatBrillouinKlein.lean
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
./lean/InfoGeometry/External/Auto/VacuumTopology.lean
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
./lean/InfoGeometry/GromovProbability.lean
./lean/InfoGeometry/GromovWittenErlangen/LieOrbitCurveWitness.lean
./lean/InfoGeometry/GW/All.lean
./lean/InfoGeometry/Hestenes/SpacetimeAlgebra.lean
./lean/InfoGeometry/HilbertTensorProduct.lean
./lean/InfoGeometry/HilbertTensorProduct/Phase2_HS2Ell2.lean
./lean/InfoGeometry/HilbertTensorProduct/Phase5_SpectralTheorem.lean
./lean/InfoGeometry/Holography/All.lean
./lean/InfoGeometry/Information/DeRhamScore.lean
./lean/InfoGeometry/JordanDecomposition/CyclicNilpotent.lean
./lean/InfoGeometry/JordanDecomposition.lean
./lean/InfoGeometry/JordanDecomposition/Scratch.lean
./lean/InfoGeometry/Kaehler/PoincareMetric.lean
./lean/InfoGeometry/KreinCarrierInstances_tmp.lean
./lean/InfoGeometry/Lie/All.lean
./lean/InfoGeometry/Measure/ProjectiveState.lean
./lean/InfoGeometry/MellinColimitTrifactor.lean
./lean/InfoGeometry/Meta/FormalLogos.lean
./lean/InfoGeometry/Meta.lean
./lean/InfoGeometry/Meta/ShadowLedger.lean
./lean/InfoGeometry/Meta/ThermodynamicGEORegulation.lean
./lean/InfoGeometry/Meta/TranscendentFunction.lean
./lean/InfoGeometry/Monster/MonsterMoonshineThermal.lean
./lean/InfoGeometry/Network/All.lean
./lean/InfoGeometry/OperatorAlgebra/ChiralCliffordSplit.lean
./lean/InfoGeometry/OperatorAlgebra/ConcreteWeylAnomaly.lean
./lean/InfoGeometry/OperatorAlgebra/OperatorialJonesCalculus.lean
./lean/InfoGeometry/OperatorAlgebra/SusceptibilityHessian.lean
./lean/InfoGeometry/OperatorAlgebra/TripotentFactorization.lean
./lean/InfoGeometry/Optics/JonesCalculus.lean
./lean/InfoGeometry/Optics/JonesCalculusSpinorLorentz.lean
./lean/InfoGeometry/Peirce/PeirceLadderOperators.lean
./lean/InfoGeometry/Physics/AlgebraicCuntzQuotient.lean
./lean/InfoGeometry/Physics/AmplituhedronPenroseTransform.lean
./lean/InfoGeometry/Physics/ChiralityPseudoscalarCuntz.lean
./lean/InfoGeometry/Physics/ChiralTensorRecoupling.lean
./lean/InfoGeometry/Physics/ChiralUncertaintyCaliber.lean
./lean/InfoGeometry/Physics/ItakuraSaitoInvariance.lean
./lean/InfoGeometry/Physics/PellisFineStructure.lean
./lean/InfoGeometry/Physics/SplitCliffordAlgebras.lean
./lean/InfoGeometry/Physics/TopologicalMTheoryGromovWitten.lean
./lean/InfoGeometry/Physics/WeylSU3ColorSymmetry.lean
./lean/InfoGeometry/Physics/ZornMatrixSU3.lean
./lean/InfoGeometry/Probability/GromovConcentration.lean
./lean/InfoGeometry/Probability/GromovFiniteCounting.lean
./lean/InfoGeometry/Probability/GromovProbability.lean
./lean/InfoGeometry/Probability/GromovProjectiveRatio.lean
./lean/InfoGeometry/Probability/GromovSystem.lean
./lean/InfoGeometry/Probability/SymmetricCounting.lean
./lean/InfoGeometry/Projective/BostConnesZetaIdentity.lean
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
./lean/InfoGeometry/Quantum/SouriauFoliation.lean
./lean/InfoGeometry/Quiver/BetheAnsatzXXZ.lean
./lean/InfoGeometry/Quiver/HbarOper.lean
./lean/InfoGeometry/Quiver/KoroteevZeitlinMirror.lean
./lean/InfoGeometry/Quiver/TKKHamiltonian.lean
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
./lean/InfoGeometry/Section27.lean
./lean/InfoGeometry/Section2.lean
./lean/InfoGeometry/Section3.lean
./lean/InfoGeometry/Section4.lean
./lean/InfoGeometry/Section5.lean
./lean/InfoGeometry/Section6.lean
./lean/InfoGeometry/Section7.lean
./lean/InfoGeometry/Section8.lean
./lean/InfoGeometry/Section9.lean
./lean/InfoGeometry/Signal/All.lean
./lean/InfoGeometry/Singular/MoorePenrose/ClosedRange.lean
./lean/InfoGeometry/Spectral/Cohomology/Gysin.lean
./lean/InfoGeometry/Spectral/Cohomology/ProjectiveSpace.lean
./lean/InfoGeometry/Spectral/Cohomology/Sandbox.lean
./lean/InfoGeometry/Spectral/Cohomology/SerreExactCouple.lean
./lean/InfoGeometry/Spectral/Cohomology/Serre.lean
./lean/InfoGeometry/Spectral/HigherGroups.lean
./lean/InfoGeometry/Spectral/RealProjective.lean
./lean/InfoGeometry/SuperMetriplectic/WeylCharacter.lean
./lean/InfoGeometry/Tessellation/All.lean
./lean/InfoGeometry/Thermo/SandboxComplexThermodynamicLiftTest.lean
./lean/InfoGeometry/Thermo/SandboxJacobianBregmanBridgeTest.lean
./lean/InfoGeometry/TKK/TKKTest.lean
./lean/InfoGeometry/Topological/All.lean
./lean/InfoGeometry/Topology/All.lean
./lean/InfoGeometry/Topology/BostConnesZetaVolume.lean
./lean/InfoGeometry/Topology/BrillouinKleinAgentVerification.lean
./lean/InfoGeometry/Topology/D4SingularityDBrane.lean
./lean/InfoGeometry/Topology/DBraneMatrixFactorization.lean
./lean/InfoGeometry/Topology/GeneralizedCircleMobius.lean
./lean/InfoGeometry/Topology/PainleveIsomonodromy.lean
./lean/InfoGeometry/Topology/SandboxMobiusSouriauThermodynamicFlowTest.lean
./lean/InfoGeometry/Topology/SandboxThermodynamicSL2MobiusFlowTest.lean
./lean/InfoGeometry/Topology/StoneCantorMathlib.lean
./lean/InfoGeometry/Topology/test_linarith.lean
./lean/InfoGeometry/TrifactorDecomposition.lean
./lean/InfoGeometry/TrifactorGeometry.lean
./lean/InfoGeometry/TrifactorProjectors.lean
./lean/InfoGeometry/Twistor/All.lean
./lean/InfoGeometry/TwistorSmoothness.lean
./lean/InfoGeometry/UnifiedMatrixBasis.lean
./lean/InfoGeometry/Wavelet/All.lean

=== Files declaring a non-InfoGeometry namespace (heuristic) ===
./lean/InfoGeometry/Algebra/BerezinianPfaffianBott.lean :: 24:namespace Audit.BerezinianPfaffianBott
./lean/InfoGeometry/Algebra/Cl11Fermions.lean :: 10:namespace Cl11Fermions
./lean/InfoGeometry/Algebra/CuntzFibonacciBraidInclusion.lean :: 15:namespace CuntzFibonacciBraidInclusion
./lean/InfoGeometry/Algebra/Det2.lean :: 4:namespace Audit
./lean/InfoGeometry/Algebra/FibonacciParafermion.lean :: 25:namespace FibonacciParafermion
./lean/InfoGeometry/Algebra/HodgeDiracDelta.lean :: 22:namespace Audit.HodgeDiracDelta
./lean/InfoGeometry/Algebra/Hypothesis1.lean :: 15:namespace Hypothesis1
./lean/InfoGeometry/Algebra/IdeleCuntzSymmetry.lean :: 11:namespace IdeleCuntz
./lean/InfoGeometry/Algebra/K0FibonacciRing.lean :: 16:namespace Audit.K0FibonacciRing
./lean/InfoGeometry/Algebra/KreinPosNegDecomposition.lean :: 20:namespace Audit.KreinPosNegDecomposition
./lean/InfoGeometry/Algebra/SuperTraceBerezinian.lean :: 5:namespace Audit.SuperTraceBerezinian
./lean/InfoGeometry/Algebra/TriFacetMatrixRealization.lean :: 6:namespace Audit.TriFacetMatrixRealization
./lean/InfoGeometry/Algebra/TriFacetSpectralPowers.lean :: 3:namespace Audit
./lean/InfoGeometry/Algebra/TripotentClSUSYBridge.lean :: 34:namespace TripotentClSUSYBridge
./lean/InfoGeometry/Algebra/UnitizationNonAssoc.lean :: 9:namespace Unitization
./lean/InfoGeometry/Algebra/VerlindeSMatrix.lean :: 26:namespace Audit.VerlindeSMatrix
./lean/InfoGeometry/Attention/LogSumExpAttention.lean :: 22:namespace AttentionIsQuantumFluid
./lean/InfoGeometry/Automath/Generated/auto_20260721_230011_1.lean :: 4:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/auto_20260721_230011_2.lean :: 4:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/causal_zorn_presheaf.lean :: 12:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/cuntz_fibonacci_resolvent.lean :: 4:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/cuntz_shift_commutativity.lean :: 4:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/cuntz_yang_baxter.lean :: 4:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/entropy_hessian_eq_fisher_inverse.lean :: 3:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/hyp_1_spectral_rigidity.lean :: 4:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/hyp_2_fibonacci_functional_calculus.lean :: 4:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/hyp_3_operator_roots.lean :: 4:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/hyp_4_braid_image.lean :: 4:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/hyp_5_k_theory.lean :: 4:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/hyp_pin55_krein.lean :: 4:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/omega_auto_omega_bost_connes_kms.lean :: 4:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/omega_auto_omega_circle_dimension.lean :: 4:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/omega_auto_omega_cuntz_shift.lean :: 4:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/omega_auto_omega_golden_ratio_seed.lean :: 4:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/omega_auto_omega_walsh_stokes.lean :: 4:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/omega_auto_omega_xi_zeta_interface.lean :: 4:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/omega_fib_complete.lean :: 5:namespace Omega.Generated
./lean/InfoGeometry/Automath/Generated/omega_fib_gcd.lean :: 3:namespace Omega.Generated
./lean/InfoGeometry/Automath/Generated/omega_fib_succ_pos.lean :: 4:namespace Omega.Generated
./lean/InfoGeometry/Automath/Generated/omega_fib_succ_succ.lean :: 4:namespace Omega.Generated
./lean/InfoGeometry/Automath/Generated/onsager_entropy_production_zero.lean :: 3:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/su3_gellmann_lie_algebra.lean :: 12:namespace Automath.Generated
./lean/InfoGeometry/Automath/Generated/test_hyp.lean :: 4:namespace Automath.Generated
./lean/InfoGeometry/Automath.lean :: 33:namespace Automath
./lean/InfoGeometry/BostConnes/BostConnesThermofield.lean :: 34:namespace BostConnesThermofield
./lean/InfoGeometry/BottPeriodicityReconciliation.lean :: 60:namespace BottPeriodicityReconciliation
./lean/InfoGeometry/Canonical/AubertPlymen.lean :: 32:namespace AubertPlymen
./lean/InfoGeometry/Canonical/BiquaternionKANnilpotent.lean :: 12:namespace BiquaternionKANnilpotent
./lean/InfoGeometry/Canonical/BiquaternionLaplaceTripotent.lean :: 13:namespace BiquaternionLaplaceTripotent
./lean/InfoGeometry/Canonical/BiquaternionNegativeRootsLog.lean :: 16:namespace BiquaternionNegativeRootsLog
./lean/InfoGeometry/Canonical/BostConnesKTheoryIntegration.lean :: 12:namespace BostConnesKTheoryIntegration
./lean/InfoGeometry/Canonical/CanonicalZornCliffordIsomorphism.lean :: 22:namespace CanonicalZornCliffordIsomorphism
./lean/InfoGeometry/Canonical/CanonicalZornCliffordRepresentation.lean :: 18:namespace CanonicalZornCliffordRepresentation
./lean/InfoGeometry/Canonical/CanonicalZornCompositionFiveGradeBridge.lean :: 26:namespace CanonicalZornCompositionFiveGradeBridge
./lean/InfoGeometry/Canonical/CanonicalZornCompositionTriality.lean :: 29:namespace CanonicalZornCompositionTriality
./lean/InfoGeometry/Canonical/CanonicalZornFiveGradedClosure.lean :: 23:namespace CanonicalZornFiveGradedClosure
./lean/InfoGeometry/Canonical/CanonicalZornIntegralSpinRepresentation.lean :: 14:namespace CanonicalZornIntegralSpinRepresentation
./lean/InfoGeometry/Canonical/CanonicalZornIntegralSpinSubgroup.lean :: 15:namespace CanonicalZornIntegralSpinSubgroup
./lean/InfoGeometry/Canonical/CanonicalZornIntegralSpinTrialityClosure.lean :: 20:namespace CanonicalZornIntegralSpinTrialityClosure
./lean/InfoGeometry/Canonical/CanonicalZornIntegralTrialityEquivariance.lean :: 16:namespace CanonicalZornIntegralTrialityEquivariance
./lean/InfoGeometry/Canonical/CanonicalZornOuterTrialityGroup.lean :: 20:namespace CanonicalZornOuterTrialityGroup
./lean/InfoGeometry/Canonical/CanonicalZornProjectiveCore.lean :: 22:namespace CanonicalZornProjectiveTKKBridge
./lean/InfoGeometry/Canonical/CanonicalZornProjectiveTKKBridge.lean :: 23:namespace CanonicalZornProjectiveTKKBridge
./lean/InfoGeometry/Canonical/CanonicalZornRealComplexSpinBaseChange.lean :: 14:namespace CanonicalZornRealComplexSpinBaseChange
./lean/InfoGeometry/Canonical/CanonicalZornRealSpin44.lean :: 24:namespace CanonicalZornRealSpin44
./lean/InfoGeometry/Canonical/CanonicalZornRealSpinTrialityClosure.lean :: 21:namespace CanonicalZornRealSpinTrialityClosure
./lean/InfoGeometry/Canonical/CanonicalZornSpinChirality.lean :: 15:namespace CanonicalZornSpinChirality
./lean/InfoGeometry/Canonical/CanonicalZornSpinRelatedFiber.lean :: 19:namespace CanonicalZornSpinRelatedFiber
./lean/InfoGeometry/Canonical/CanonicalZornUnifiedClosure.lean :: 19:namespace CanonicalZornUnifiedClosure
./lean/InfoGeometry/Canonical/CliffordCantorModeHierarchy.lean :: 14:namespace CliffordCantorModeHierarchy
./lean/InfoGeometry/Canonical/ConcreteSuperVirasoroColimitReadback.lean :: 36:namespace ConcreteSuperVirasoroColimitReadback
./lean/InfoGeometry/Canonical/ConformalSubalgebraDebt.lean :: 20:namespace ConformalSubalgebra
./lean/InfoGeometry/Canonical/ConnesRadonNikodymCocycle.lean :: 48:namespace ConnesCocycle
./lean/InfoGeometry/Canonical/CyclicCocycleCantor.lean :: 22:namespace CyclicCocycleCantor
./lean/InfoGeometry/Canonical/FibonacciAnyonSimilarity.lean :: 19:namespace FibonacciAnyons.Similarity
./lean/InfoGeometry/Canonical/InductiveOperatorTaylorClosure.lean :: 24:namespace InductiveOperatorTaylorClosure
./lean/InfoGeometry/Canonical/IntegralZornBilinearComposition.lean :: 23:namespace IntegralZornBilinearComposition
./lean/InfoGeometry/Canonical/IntegralZornCompositionAlgebra.lean :: 15:namespace IntegralZornCompositionAlgebra
./lean/InfoGeometry/Canonical/IntegralZornII44Bridge.lean :: 24:namespace IntegralZornII44Bridge
./lean/InfoGeometry/Canonical/JaynesFormalism.lean :: 28:namespace JaynesFormalism
./lean/InfoGeometry/Canonical/KMSBoundaryTrajectory.lean :: 55:namespace KMSBoundaryTrajectory
./lean/InfoGeometry/Canonical/PrimeCocycleCoefficients.lean :: 32:namespace PrimeCocycleCoefficients
./lean/InfoGeometry/Canonical/ProjectiveAffineConformalClosure55.lean :: 17:namespace ProjectiveAffineConformalClosure55
./lean/InfoGeometry/Canonical/TKKJordanPairData.lean :: 21:namespace TKKJordanPairData
./lean/InfoGeometry/Canonical/WeylCantorSynthesis.lean :: 55:namespace WeylCantorSynthesis
./lean/InfoGeometry/Canonical/WeylIntegrationFixedPoint.lean :: 65:namespace WeylIntegrationFixedPoint
./lean/InfoGeometry/Canonical/ZornCellComposition.lean :: 24:namespace ZornCell
./lean/InfoGeometry/Canonical/ZornCore.lean :: 13:namespace ZornCore
./lean/InfoGeometry/Canonical/ZornOuterTrialityGroup.lean :: 11:namespace ZornOuterTrialityGroup
./lean/InfoGeometry/Canonical/ZornTrialityTKKBridge.lean :: 20:namespace ZornTrialityTKKBridge
./lean/InfoGeometry/Categorical/ZornBraidColimitKMS.lean :: 51:namespace ZornBraidColimitKMS
./lean/InfoGeometry/DeterminantTrifactor.lean :: 18:namespace DeterminantTrifactor
./lean/InfoGeometry/E8/E8TrialityThermalProtection.lean :: 28:namespace E8Triality
./lean/InfoGeometry/ErlangenCoordinateless.lean :: 36:namespace ErlangenCoordinateless
./lean/InfoGeometry/Eval/SeedProverSmoke.lean :: 5:namespace SeedProverSmoke
./lean/InfoGeometry/Experimental/WeylCantorFock.lean :: 47:namespace WeylCantorFock
./lean/InfoGeometry/Experimental/WeylIntegrationFormula.lean :: 61:namespace WeylIntegration
./lean/InfoGeometry/External/Auto/A35MirrorNuclei.lean :: 3:namespace A35MirrorNuclei
./lean/InfoGeometry/External/Auto/A47KIsospinMixing.lean :: 5:namespace A47KIsospinMixing
./lean/InfoGeometry/External/Auto/A47MirrorNuclei.lean :: 6:namespace A47MirrorNuclei
./lean/InfoGeometry/External/Auto/A67MirrorE1.lean :: 13:namespace A67MirrorE1
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
./lean/InfoGeometry/External/Auto/BiquaternionLaplaceTripotent.lean :: 18:namespace BiquaternionLaplaceTripotent
./lean/InfoGeometry/External/Auto/BiquaternionMobiusSquashing.lean :: 13:namespace BiquaternionMobiusSquashing
./lean/InfoGeometry/External/Auto/BiquaternionNegativeRootsLog.lean :: 16:namespace BiquaternionNegativeRootsLog
./lean/InfoGeometry/External/Auto/BirkhoffInformationGeometry.lean :: 3:namespace BirkhoffInformationGeometry
./lean/InfoGeometry/External/Auto/BisoiForbiddenE1Mixing.lean :: 5:namespace BisoiForbiddenE1Mixing
./lean/InfoGeometry/External/Auto/BizzetiA67IVGMR.lean :: 6:namespace BizzetiA67IVGMR
./lean/InfoGeometry/External/Auto/BlackHoleHolography.lean :: 14:namespace BlackHoleHolography
./lean/InfoGeometry/External/Auto/BM1MirrorNuclei.lean :: 13:namespace BM1MirrorNuclei
./lean/InfoGeometry/External/Auto/BogoliubovBraidGraphWeld.lean :: 23:namespace BogoliubovBraidGraphWeld
./lean/InfoGeometry/External/Auto/BostConnesDeformation.lean :: 8:namespace BostConnesDeformation
./lean/InfoGeometry/External/Auto/BPSPositiveEnergyBound.lean :: 5:namespace BPSPositiveEnergyBound
./lean/InfoGeometry/External/Auto/BraidedCocycleWilsonEntropy.lean :: 11:namespace BraidedCocycleWilsonEntropy
./lean/InfoGeometry/External/Auto/BraidInductiveColimitCategory.lean :: 15:namespace BraidInductiveColimitComplement
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
./lean/InfoGeometry/External/Auto/CayleySchreierGauge.lean :: 12:namespace CayleySchreierGauge
./lean/InfoGeometry/External/Auto/ChemicalPotentialMetricBridge.lean :: 12:namespace ChemicalPotentialMetricBridge
./lean/InfoGeometry/External/Auto/ChiralAffineBogoliubovWeld.lean :: 24:namespace ChiralAffineBogoliubovWeld
./lean/InfoGeometry/External/Auto/ChiralCuntzInductive.lean :: 20:namespace ChiralCuntzInductive
./lean/InfoGeometry/External/Auto/CKMAeonColimit.lean :: 5:namespace CKMAeonColimit
./lean/InfoGeometry/External/Auto/CliffordInductiveTripotent.lean :: 13:namespace CliffordInductiveTripotent
./lean/InfoGeometry/External/Auto/CognitiveVacuum.lean :: 4:namespace AgentBrain
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
./lean/InfoGeometry/External/Auto/CuntzKTheoryPairing.lean :: 7:namespace CuntzKTheoryPairing
./lean/InfoGeometry/External/Auto/D4TrialityUniverse.lean :: 23:namespace D4TrialityUniverse
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
./lean/InfoGeometry/External/Auto/FureyLadderSerreResidues.lean :: 5:namespace FureyLadderSerreResidues
./lean/InfoGeometry/External/Auto/FusOctonionKKS.lean :: 5:namespace FusOctonionKKS
./lean/InfoGeometry/External/Auto/GellMannCartan.lean :: 13:namespace GellMannCartan
./lean/InfoGeometry/External/Auto/GeneralizedMirrorNuclei.lean :: 16:namespace GeneralizedMirrorNuclei
./lean/InfoGeometry/External/Auto/GlideDiracSelectionRule.lean :: 20:namespace GlideDiracSelectionRule
./lean/InfoGeometry/External/Auto/GlideModularJ.lean :: 18:namespace GlideModularJ
./lean/InfoGeometry/External/Auto/GlideSuperchargeCasimir.lean :: 17:namespace GlideSuperchargeCasimir
./lean/InfoGeometry/External/Auto/GlideSymmetricInvariant.lean :: 13:namespace GlideSymmetricInvariant
./lean/InfoGeometry/External/Auto/GNSConstruction.lean :: 52:namespace State
./lean/InfoGeometry/External/Auto/GNSModularObservables.lean :: 20:namespace GNSModularObservables
./lean/InfoGeometry/External/Auto/GNSQuotientFinite.lean :: 18:namespace GNSQuotientFinite
./lean/InfoGeometry/External/Auto/GohbergKreinIndex.lean :: 13:namespace GohbergKreinIndex
./lean/InfoGeometry/External/Auto/GoldenCCR.lean :: 16:namespace GoldenCCR
./lean/InfoGeometry/External/Auto/GoldenSpectralTriple.lean :: 13:namespace GoldenSpectralTriple
./lean/InfoGeometry/External/Auto/GoutevTonevPrinciple.lean :: 20:namespace GoutevTonevPrinciple
./lean/InfoGeometry/External/Auto/GrandHolographicTheorem.lean :: 19:namespace GrandHolographicTheorem
./lean/InfoGeometry/External/Auto/GravitySoldering.lean :: 12:namespace GravitySoldering
./lean/InfoGeometry/External/Auto/GT_FromText.lean :: 15:namespace GT.Extracted
./lean/InfoGeometry/External/Auto/GuptaAdaptVQERandomHamiltonians.lean :: 5:namespace GuptaAdaptVQERandomHamiltonians
./lean/InfoGeometry/External/Auto/HeavyIsospinMixingSystematics.lean :: 7:namespace HeavyIsospinMixingSystematics
./lean/InfoGeometry/External/Auto/HestenesKreinColimitBridge.lean :: 22:namespace HestenesKreinColimitBridge
./lean/InfoGeometry/External/Auto/HolographicArchitect.lean :: 1:namespace HolographicArchitect
./lean/InfoGeometry/External/Auto/HolographicErlangenCompletion.lean :: 13:namespace HolographicErlangenCompletion
./lean/InfoGeometry/External/Auto/HolographicScaleExtinctions.lean :: 12:namespace HolographicScaleExtinctions
./lean/InfoGeometry/External/Auto/HoTTInfinityBridge.lean :: 6:namespace HoTTInfinityBridge
./lean/InfoGeometry/External/Auto/ImprovedLLMTheory.lean :: 6:namespace ImprovedLLMTheory
./lean/InfoGeometry/External/Auto/InformationGeometricCutoff.lean :: 17:namespace InformationGeometricCutoff
./lean/InfoGeometry/External/Auto/InstantonQCD.lean :: 5:namespace QCD_Instanton
./lean/InfoGeometry/External/Auto/IsospinSymmetryBreaking.lean :: 4:namespace IsospinSymmetryBreaking
./lean/InfoGeometry/External/Auto/JaynesLDDPGNSColimit.lean :: 18:namespace JaynesLDDPGNSColimit
./lean/InfoGeometry/External/Auto/JaynesLeanColimitBridge.lean :: 24:namespace JaynesLeanColimitBridge
./lean/InfoGeometry/External/Auto/JordanBlock2.lean :: 5:namespace JordanBlock2
./lean/InfoGeometry/External/Auto/KanekoA67HighSpinMED.lean :: 5:namespace KanekoA67HighSpinMED
./lean/InfoGeometry/External/Auto/KaneMeleOrbifold.lean :: 4:namespace KaneMeleOrbifold
./lean/InfoGeometry/External/Auto/KANFourierMellinDirac.lean :: 20:namespace KANFourierMellinDirac
./lean/InfoGeometry/External/Auto/KasparovKreinDoubling.lean :: 12:namespace KasparovKrein
./lean/InfoGeometry/External/Auto/KleinGeometrySupergraded.lean :: 12:namespace KleinGeometrySupergraded
./lean/InfoGeometry/External/Auto/KleinGrapheneTunneling.lean :: 22:namespace KleinGrapheneTunneling
./lean/InfoGeometry/External/Auto/KoroteevZeitlin3DMirror.lean :: 13:namespace KoroteevZeitlin
./lean/InfoGeometry/External/Auto/LECM2022ElectroweakRadiiISB.lean :: 5:namespace LECM2022ElectroweakRadiiISB
./lean/InfoGeometry/External/Auto/LegendreFenchelSpectralGap.lean :: 18:namespace LegendreFenchelSpectralGap
./lean/InfoGeometry/External/Auto/LicataFinsterEMSpaces.lean :: 16:namespace LicataFinsterEMSpaces
./lean/InfoGeometry/External/Auto/LightConeTripotentMatrixBridge.lean :: 21:namespace LightConeTripotentMatrixBridge
./lean/InfoGeometry/External/Auto/LiuCollinsAffineInvariance.lean :: 12:namespace LiuCollins
./lean/InfoGeometry/External/Auto/LlewellynZr79MED.lean :: 5:namespace LlewellynZr79MED
./lean/InfoGeometry/External/Auto/LogDetSuperKahlerBarrier.lean :: 17:namespace LogDetSuperKahlerBarrier
./lean/InfoGeometry/External/Auto/MajoranaPrimonSpectralBridge.lean :: 18:namespace MajoranaPrimonSpectralBridge
./lean/InfoGeometry/External/Automath/SpectralSquashCayleyDKT.lean :: 14:namespace SpectralSquashCayleyDKT
./lean/InfoGeometry/External/Auto/MellinWaveletScaleShiftDigest.lean :: 27:namespace MellinWaveletScaleShiftDigest
./lean/InfoGeometry/External/Auto/MetriplecticCausality.lean :: 13:namespace MetriplecticCausality
./lean/InfoGeometry/External/Auto/MinkowskiBiquaternion.lean :: 10:namespace MinkowskiBiquaternion
./lean/InfoGeometry/External/Auto/MITFInvariant.lean :: 22:namespace MITFInvariant
./lean/InfoGeometry/External/Auto/MITFOrientabilityFlow.lean :: 17:namespace MITF
./lean/InfoGeometry/External/Auto/MITFOrientability.lean :: 25:namespace MITF
./lean/InfoGeometry/External/Auto/MobiusWittenIndex.lean :: 15:namespace MobiusWittenIndex
./lean/InfoGeometry/External/Auto/MobiusWittenKleinIndex.lean :: 15:namespace MobiusWittenKleinIndex
./lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean :: 5:namespace ModularAgingFlavor
./lean/InfoGeometry/External/Auto/ModularAutomorphismGroup.lean :: 19:namespace ModularAutomorphismGroup
./lean/InfoGeometry/External/Auto/ModularGlideCPT.lean :: 20:namespace ModularGlideCPT
./lean/InfoGeometry/External/Auto/ModularHolographicMetric.lean :: 18:namespace ModularHolographicMetric
./lean/InfoGeometry/External/Auto/ModularItakuraBiquaternion.lean :: 21:namespace ModularItakuraBiquaternion
./lean/InfoGeometry/External/Auto/ModularKreinReflectionColimit.lean :: 17:namespace ModularKreinReflectionColimit
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
./lean/InfoGeometry/External/Auto/NuclearPhononGenerators.lean :: 5:namespace NuclearPhononGenerators
./lean/InfoGeometry/External/Auto/NuclearPhononMetriplecticBridge.lean :: 6:namespace NuclearPhononMetriplecticBridge
./lean/InfoGeometry/External/Auto/NumberSystemColimits.lean :: 4:namespace NumberSystemLadder
./lean/InfoGeometry/External/Auto/OakuTakayamaDModuleDeRham.lean :: 25:namespace OakuTakayamaDModuleDeRham
./lean/InfoGeometry/External/Auto/OctonionMatrixEncodings.lean :: 21:namespace OctonionMatrixEncodings
./lean/InfoGeometry/External/Auto/OrlandiA67Proceedings.lean :: 5:namespace OrlandiA67Proceedings
./lean/InfoGeometry/External/Auto/PaperwallDiscreteSUSY.lean :: 13:namespace PaperwallDiscreteSUSY
./lean/InfoGeometry/External/Auto/PaperwallHolographicSUSY.lean :: 18:namespace PaperwallHolographicSUSY
./lean/InfoGeometry/External/Auto/PaperwallSUSY.lean :: 12:namespace PaperwallSUSY
./lean/InfoGeometry/External/Auto/PauliZornTrifactor.lean :: 21:namespace PauliZornTrifactor
./lean/InfoGeometry/External/Auto/PenroseCuntzKriegerHolography.lean :: 5:namespace PenroseCuntzKriegerHolography
./lean/InfoGeometry/External/Auto/PenroseKMSSpectralDimension.lean :: 17:namespace PenroseKMSSpectralDimension
./lean/InfoGeometry/External/Auto/PenroseSpinIncidenceTessellation.lean :: 14:namespace PenroseSpinIncidenceTessellation
./lean/InfoGeometry/External/Auto/PentagonPenroseWallpaperFractal.lean :: 19:namespace PentagonPenroseWallpaperFractal
./lean/InfoGeometry/External/Auto/PolynomialSymmetryOperators.lean :: 10:namespace PolynomialSymmetry
./lean/InfoGeometry/External/Auto/PrimaMateriaInformationGeometry.lean :: 9:namespace PrimaMateria
./lean/InfoGeometry/External/Auto/PrimeMellinSymplecticCAR.lean :: 8:namespace PrimeMellinSymplecticCAR
./lean/InfoGeometry/External/Auto/PrimonBosonFermionDuality.lean :: 24:namespace PrimonBosonFermionDuality
./lean/InfoGeometry/External/Auto/PrimonFockTraceBridge.lean :: 22:namespace PrimonFockTraceBridge
./lean/InfoGeometry/External/Auto/PrimonHilbertPolyaSeparation.lean :: 21:namespace PrimonHilbertPolyaSeparation
./lean/InfoGeometry/External/Auto/PrimonSuperThermodynamics.lean :: 8:namespace PrimonSuperThermo
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
./lean/InfoGeometry/External/Auto/QRootOfUnityTruncation.lean :: 20:namespace QRootOfUnityTruncation
./lean/InfoGeometry/External/Auto/QuadraticConfiguration3.lean :: 27:namespace QuadraticConfiguration3
./lean/InfoGeometry/External/Auto/QuadricConf3BraidingCooperadBridge.lean :: 11:namespace QuadricConf3BraidingCooperadBridge
./lean/InfoGeometry/External/Auto/RegularizationCayleyPipeline.lean :: 16:namespace RegularizationCayleyPipeline
./lean/InfoGeometry/External/Auto/RelativeModularStateDikin.lean :: 22:namespace RelativeModularStateDikin
./lean/InfoGeometry/External/Auto/RelativisticBiquaternionKAN.lean :: 21:namespace RelativisticBiquaternionKAN
./lean/InfoGeometry/External/Auto/RescaledPhaseVolumeCanonical.lean :: 17:namespace RescaledPhaseVolumeCanonical
./lean/InfoGeometry/External/Auto/RGFixedPoint.lean :: 13:namespace RGFixedPoint
./lean/InfoGeometry/External/Auto/RiemannKleinDuality.lean :: 14:namespace RiemannKleinDuality
./lean/InfoGeometry/External/Auto/RP3Octupole.lean :: 12:namespace RP3Topology
./lean/InfoGeometry/External/Auto/S3ColorSpinorDecomposition.lean :: 14:namespace S3ColorSpinorDecomposition
./lean/InfoGeometry/External/Auto/SarkarTwoLevelIsospinMixing.lean :: 5:namespace SarkarTwoLevelIsospinMixing
./lean/InfoGeometry/External/Auto/SarsArangoBridge.lean :: 3:namespace SarsArangoBridge
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
./lean/InfoGeometry/External/Auto/SerreSpectralSplitOctonion.lean :: 5:namespace SerreSpectralSplitOctonion
./lean/InfoGeometry/External/Auto/SheikhIsospinSymmetryBreaking.lean :: 5:namespace SheikhIsospinSymmetryBreaking
./lean/InfoGeometry/External/Auto/SmithHatIsingDuality.lean :: 16:namespace SmithHatIsingDuality
./lean/InfoGeometry/External/Auto/SO55NullSU5KleinSpectral.lean :: 5:namespace SO55NullSU5KleinSpectral
./lean/InfoGeometry/External/Auto/SolovievQPNMChiralCuntz.lean :: 33:namespace SolovievQPNMChiralCuntz
./lean/InfoGeometry/External/Auto/SouriauBiquaternionGaussian.lean :: 14:namespace SouriauBiquaternionGaussian
./lean/InfoGeometry/External/Auto/SouriauCasimirEntropyLeaves.lean :: 6:namespace SouriauCasimirEntropyLeaves
./lean/InfoGeometry/External/Auto/SouriauGaussian.lean :: 12:namespace SouriauGaussian
./lean/InfoGeometry/External/Auto/SouriauHestenesMobiusPole.lean :: 22:namespace SouriauHestenesMobiusPole
./lean/InfoGeometry/External/Auto/SouriauOperatorThermodynamics.lean :: 20:namespace SouriauOperatorThermodynamics
./lean/InfoGeometry/External/Auto/SouriauThermoColimit.lean :: 22:namespace SouriauThermoColimit
./lean/InfoGeometry/External/Auto/SpacetimeIsSpin.lean :: 17:namespace SpacetimeIsSpin
./lean/InfoGeometry/External/Auto/SpinorMonodromySteppingStone.lean :: 22:namespace SpinorMonodromySteppingStone
./lean/InfoGeometry/External/Auto/SpinorVectorDuality.lean :: 8:namespace V4
./lean/InfoGeometry/External/Auto/SplitOctonionMinkowski.lean :: 23:namespace SplitOctonionMinkowski
./lean/InfoGeometry/External/Auto/SplitOctonionNilpotent.lean :: 12:namespace SplitOctonionNilpotent
./lean/InfoGeometry/External/Auto/SplitOctonionZornKKS.lean :: 5:namespace SplitOctonionZornKKS
./lean/InfoGeometry/External/Auto/SquashingOperator.lean :: 12:namespace SquashingOperator
./lean/InfoGeometry/External/Auto/StrongCPAeonTheta.lean :: 5:namespace StrongCPAeonTheta
./lean/InfoGeometry/External/Auto/SU3LoopBraidDuality.lean :: 34:namespace SU3LoopBraidDuality
./lean/InfoGeometry/External/Auto/SUNLoopBraidCuntzBoundary.lean :: 22:namespace SUNLoopBraidCuntzBoundary
./lean/InfoGeometry/External/Auto/SuperBerezinianKlein.lean :: 18:namespace SuperBerezinianKlein
./lean/InfoGeometry/External/Auto/SuperchargeSquare.lean :: 16:namespace SuperchargeSquare
./lean/InfoGeometry/External/Auto/SymbolicFockLane.lean :: 25:namespace SymbolicFockLane
./lean/InfoGeometry/External/Auto/SymbolicLaneUHFBridge.lean :: 19:namespace SymbolicLaneUHFBridge
./lean/InfoGeometry/External/Auto/SymmetryReviewISB.lean :: 5:namespace SymmetryReviewISB
./lean/InfoGeometry/External/Auto/ThesisMaster.lean :: 22:namespace ThesisMaster
./lean/InfoGeometry/External/Auto/ThreeDMirrorSymmetry.lean :: 8:namespace ThreeDMirrorSymmetry
./lean/InfoGeometry/External/Auto/TitsBruhatBrillouinKlein.lean :: 26:namespace TitsBruhatBrillouinKlein
./lean/InfoGeometry/External/Auto/TKKCartanDecomposition.lean :: 11:namespace TKKCartanDecomposition
./lean/InfoGeometry/External/Auto/TKKCompileData.lean :: 18:namespace TKKCompileData
./lean/InfoGeometry/External/Auto/TKKQQBridge.lean :: 6:namespace TKKQQBridge
./lean/InfoGeometry/External/Auto/TKK_StandardModel.lean :: 13:namespace TKK_StandardModel
./lean/InfoGeometry/External/Auto/TPUAQLattice.lean :: 3:namespace AutonomousHypothesisEngine
./lean/InfoGeometry/External/Auto/TrifactorGeometry.lean :: 20:namespace TrifactorGeometry
./lean/InfoGeometry/External/Auto/TripotentCliffordColimit.lean :: 22:namespace TripotentCliffordColimit
./lean/InfoGeometry/External/Auto/TripotentPenroseHolography.lean :: 12:namespace TripotentPenrose
./lean/InfoGeometry/External/Auto/UHFInductiveColimit.lean :: 22:namespace UHFInductiveColimit
./lean/InfoGeometry/External/Auto/UnifiedKleinHolographicArchitecture.lean :: 15:namespace UnifiedKleinHolographicArchitecture
./lean/InfoGeometry/External/Auto/UthayakumaarMirrorKnockout.lean :: 5:namespace UthayakumaarMirrorKnockout
./lean/InfoGeometry/External/Auto/VacuumCohomology.lean :: 12:namespace VacuumCohomology
./lean/InfoGeometry/External/Auto/VacuumGroundstate.lean :: 7:namespace VacuumGroundstate
./lean/InfoGeometry/External/Auto/VacuumJonesKleinBirefringence.lean :: 17:namespace VacuumJonesKleinBirefringence
./lean/InfoGeometry/External/Auto/VacuumTopology.lean :: 7:namespace VacuumTopology
./lean/InfoGeometry/External/Auto/VarlamovKleinSpectral.lean :: 5:namespace VarlamovKleinSpectral
./lean/InfoGeometry/External/Auto/VerberckWallpaperFourier.lean :: 23:namespace VerberckWallpaperFourier
./lean/InfoGeometry/External/Auto/VertexAlgebraBraidingCocycle.lean :: 23:namespace VertexAlgebraBraidingCocycle
./lean/InfoGeometry/External/Auto/WallpaperBulkAnyonProjection.lean :: 20:namespace WallpaperBulkAnyonProjection
./lean/InfoGeometry/External/Auto/WallpaperClassification.lean :: 12:namespace WallpaperClassification
./lean/InfoGeometry/External/Auto/WallpaperCohomology.lean :: 29:namespace WallpaperCohomology
./lean/InfoGeometry/External/Auto/WallpaperFermionSuperconductingGap.lean :: 28:namespace WallpaperFermionSuperconductingGap
./lean/InfoGeometry/External/Auto/WallpaperIsometry.lean :: 9:namespace WallpaperIsometry
./lean/InfoGeometry/External/Auto/WallpaperMetamaterialDataset.lean :: 17:namespace WallpaperMetamaterialDataset
./lean/InfoGeometry/External/Auto/WallpaperSemidirectProduct.lean :: 13:namespace WallpaperSemidirectProduct
./lean/InfoGeometry/External/Auto/WarehamCGADilatorSL2.lean :: 5:namespace WarehamCGADilatorSL2
./lean/InfoGeometry/External/Auto/WarehamNullBasis55.lean :: 3:namespace WarehamNullBasis55
./lean/InfoGeometry/External/Auto/WeakIsospinSU2.lean :: 9:namespace WeakIsospinSU2
./lean/InfoGeometry/External/Auto/WeylGaugeItakuraSaito.lean :: 5:namespace WeylGaugeItakuraSaito
./lean/InfoGeometry/External/Auto/WittenIndex.lean :: 4:namespace AnomalyCancellation
./lean/InfoGeometry/External/Auto/YanevaPd94PnSymmetry.lean :: 5:namespace YanevaPd94PnSymmetry
./lean/InfoGeometry/External/Auto/YangBaxterQuotientDescent.lean :: 14:namespace YangBaxterQuotientDescent
./lean/InfoGeometry/External/Auto/ZetaInformationGeometry.lean :: 7:namespace ZetaInformationGeometry
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
./lean/InfoGeometry/HilbertTensorProduct.lean :: 6:namespace HilbertTensorProduct
./lean/InfoGeometry/HilbertTensorProduct/Phase2_HS2Ell2.lean :: 18:namespace HilbertTensorProduct
./lean/InfoGeometry/HilbertTensorProduct/Phase5_SpectralTheorem.lean :: 18:namespace HilbertTensorProduct.SpectralTheorem
./lean/InfoGeometry/JordanDecomposition.lean :: 23:namespace JordanDecomposition
./lean/InfoGeometry/MellinColimitTrifactor.lean :: 19:namespace MellinColimitTrifactor
./lean/InfoGeometry/Meta/FormalLogos.lean :: 45:namespace Meta.FormalLogos
./lean/InfoGeometry/Meta/ShadowLedger.lean :: 33:namespace Meta.ShadowLedger
./lean/InfoGeometry/Meta/ThermodynamicGEORegulation.lean :: 31:namespace Meta.ThermodynamicGEORegulation
./lean/InfoGeometry/Meta/TranscendentFunction.lean :: 49:namespace Meta.TranscendentFunction
./lean/InfoGeometry/Monster/MonsterMoonshineThermal.lean :: 17:namespace MonsterMoonshine
./lean/InfoGeometry/Optics/JonesCalculus.lean :: 20:namespace JonesCalulus
./lean/InfoGeometry/Optics/JonesCalculusSpinorLorentz.lean :: 7:namespace JonesCalculus
./lean/InfoGeometry/Peirce/PeirceLadderOperators.lean :: 22:namespace PeirceLadder
./lean/InfoGeometry/Physics/AlgebraicCuntzQuotient.lean :: 25:namespace AlgebraicCuntzQuotient
./lean/InfoGeometry/Physics/AmplituhedronPenroseTransform.lean :: 13:namespace Amplituhedron
./lean/InfoGeometry/Physics/ChiralityPseudoscalarCuntz.lean :: 11:namespace ChiralityPseudoscalar
./lean/InfoGeometry/Physics/ChiralTensorRecoupling.lean :: 24:namespace ChiralTensorRecoupling
./lean/InfoGeometry/Physics/ChiralUncertaintyCaliber.lean :: 14:namespace ChiralUncertainty
./lean/InfoGeometry/Physics/PellisFineStructure.lean :: 19:namespace PellisFineStructure
./lean/InfoGeometry/Physics/SplitCliffordAlgebras.lean :: 37:namespace SplitClifford
./lean/InfoGeometry/Physics/TopologicalMTheoryGromovWitten.lean :: 11:namespace TopologicalMTheory
./lean/InfoGeometry/Physics/WeylSU3ColorSymmetry.lean :: 23:namespace WeylSU3ColorSymmetry
./lean/InfoGeometry/Probability/GromovConcentration.lean :: 20:namespace Gromov.Concentration
./lean/InfoGeometry/Probability/GromovFiniteCounting.lean :: 35:namespace Gromov.Probability
./lean/InfoGeometry/Probability/GromovProbability.lean :: 20:namespace GromovProbability
./lean/InfoGeometry/Probability/GromovProjectiveRatio.lean :: 23:namespace GromovSystem
./lean/InfoGeometry/Probability/GromovSystem.lean :: 27:namespace GromovSystem
./lean/InfoGeometry/Probability/SymmetricCounting.lean :: 21:namespace SymmetricCounting
./lean/InfoGeometry/Projective/QuantumTwistorDirac.lean :: 20:namespace QuantumTwistorDirac
./lean/InfoGeometry/Quantum/FibonacciFusionCategory.lean :: 38:namespace FibonacciFusion
./lean/InfoGeometry/Quiver/BetheAnsatzXXZ.lean :: 16:namespace KoroteevZeitlin.Bethe
./lean/InfoGeometry/Quiver/HbarOper.lean :: 18:namespace KoroteevZeitlin.Oper
./lean/InfoGeometry/Quiver/KoroteevZeitlinMirror.lean :: 31:namespace KoroteevZeitlin
./lean/InfoGeometry/Quiver/TKKHamiltonian.lean :: 7:namespace TKKHamiltonian
./lean/InfoGeometry/Routing/BirkhoffVonNeumann.lean :: 13:namespace BirkhoffRouting
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
./lean/InfoGeometry/Section27.lean :: 47:namespace Section27
./lean/InfoGeometry/Section2.lean :: 13:namespace Section2
./lean/InfoGeometry/Section3.lean :: 39:namespace Section3
./lean/InfoGeometry/Section4.lean :: 16:namespace Section4
./lean/InfoGeometry/Section5.lean :: 12:namespace Section5
./lean/InfoGeometry/Section6.lean :: 14:namespace Section6
./lean/InfoGeometry/Section7.lean :: 17:namespace Section7
./lean/InfoGeometry/Section8.lean :: 22:namespace Section8
./lean/InfoGeometry/Section9.lean :: 29:namespace Section9
./lean/InfoGeometry/SuperMetriplectic/WeylCharacter.lean :: 22:namespace WeylCharacterGibbsPacket
./lean/InfoGeometry/Topology/D4SingularityDBrane.lean :: 32:namespace D4MatrixFactorization
./lean/InfoGeometry/Topology/DBraneMatrixFactorization.lean :: 26:namespace MatrixFactorization
./lean/InfoGeometry/Topology/GeneralizedCircleMobius.lean :: 20:namespace GeneralizedCircle
./lean/InfoGeometry/Topology/PainleveIsomonodromy.lean :: 35:namespace PainleveIsomonodromy
./lean/InfoGeometry/TrifactorDecomposition.lean :: 10:namespace TrifactorDecomposition
./lean/InfoGeometry/TrifactorGeometry.lean :: 12:namespace TrifactorGeometry
./lean/InfoGeometry/TrifactorProjectors.lean :: 15:namespace TrifactorProjectors
./lean/InfoGeometry/TwistorSmoothness.lean :: 21:namespace TwistorSmoothness
./lean/InfoGeometry/UnifiedMatrixBasis.lean :: 14:namespace UnifiedMatrixBasis

=== Namespace prefix histogram (first namespace line per file) ===
   3901 InfoGeometry
     30 Bridge
     23 Automath
     22 VirasoroProject
     18 ZornCell
     12 CertifiedInverseKernel
     10 SymmetricLieAlgebra
     10 Audit
      9 PhaseLinear
      8 ZornMatrix
      8 GromovWittenErlangen
      8 ConformalInference
      6 Tensor
      6 RawCARModeCompletion
      6 IsDrazinInverse
      6 CertifiedConformalInference
      6 Canonical
      5 ZornProjectiveDatum
      5 RealSplitKreinKasparovCycle
      5 LieTwoCocycle
      5 CyclicAlgebraicState
      4 TKKGrade
      4 Projective
      4 PositiveMeasure
      4 PolarDatum
      4 Plucker6
      4 Physics
      4 Omega
      4 Meta
      4 KoroteevZeitlin

[audit] Done.
```

## Orphaned Lean file audit

```text
[orphaned-check] Orphaned top-level Lean file in lean/: ast_export_test.lean
```

## Quarantine Boundary Audit

```text
Forbidden quarantined import: InfoGeometry.Canonical.AQFTOperatorInterface in lean/InfoGeometry/CoverageClosure.lean:78
Forbidden quarantined import: InfoGeometry.Canonical.AQFTOperatorInterface in lean/InfoGeometry/All.lean:548
Forbidden quarantined import: InfoGeometry.Canonical.AnomalyDilationBridge in lean/InfoGeometry/CoverageClosure.lean:81
Forbidden quarantined import: InfoGeometry.Canonical.AnomalyDilationBridge in lean/InfoGeometry/All.lean:571
Forbidden quarantined import: InfoGeometry.Canonical.BeliefDynamics in lean/InfoGeometry/CoverageClosure.lean:89
Forbidden quarantined import: InfoGeometry.Canonical.BeliefDynamics in lean/InfoGeometry/All.lean:622
Forbidden quarantined import: InfoGeometry.Canonical.BerryPhase in lean/InfoGeometry/CoverageClosure.lean:91
Forbidden quarantined import: InfoGeometry.Canonical.BerryPhase in lean/InfoGeometry/All.lean:630
Forbidden quarantined import: InfoGeometry.Canonical.BerryPhase in lean/InfoGeometry/Canonical/BerryHolonomy.lean:1
Forbidden quarantined import: InfoGeometry.Canonical.CalabiYauBridge in lean/InfoGeometry/All.lean:731
Forbidden quarantined import: InfoGeometry.Canonical.CalabiYauBridge in lean/InfoGeometry/CoverageClosure.lean:103
Forbidden quarantined import: InfoGeometry.Canonical.CalabiYauBridge in lean/InfoGeometry/Canonical/CalabiYauGrandDualityBridge.lean:1
Forbidden quarantined import: InfoGeometry.Canonical.ChiralAction in lean/InfoGeometry/Quantum/DoubleCopyBridge.lean:4
Forbidden quarantined import: InfoGeometry.Canonical.ChiralAction in lean/InfoGeometry/CoverageClosure.lean:113
Forbidden quarantined import: InfoGeometry.Canonical.ChiralAction in lean/InfoGeometry/All.lean:831
Forbidden quarantined import: InfoGeometry.Canonical.ChiralCliffordBridge in lean/InfoGeometry/CoverageClosure.lean:116
Forbidden quarantined import: InfoGeometry.Canonical.ChiralCliffordBridge in lean/InfoGeometry/All.lean:837
Forbidden quarantined import: InfoGeometry.Canonical.ConformalWard in lean/InfoGeometry/CoverageClosure.lean:133
Forbidden quarantined import: InfoGeometry.Canonical.ConformalWard in lean/InfoGeometry/All.lean:938
Forbidden quarantined import: InfoGeometry.Canonical.DiracRicciBridge in lean/InfoGeometry/CoverageClosure.lean:148
Forbidden quarantined import: InfoGeometry.Canonical.DiracRicciBridge in lean/InfoGeometry/All.lean:1014
Forbidden quarantined import: InfoGeometry.Canonical.GrandSynthesis in lean/InfoGeometry/CoverageClosure.lean:191
Forbidden quarantined import: InfoGeometry.Canonical.GrandSynthesis in lean/InfoGeometry/All.lean:1228
Forbidden quarantined import: InfoGeometry.Canonical.GrandUnificationBlueprint in lean/InfoGeometry/CoverageClosure.lean:192
Forbidden quarantined import: InfoGeometry.Canonical.GrandUnificationBlueprint in lean/InfoGeometry/All.lean:1234
Forbidden quarantined import: InfoGeometry.Canonical.HolographicEmergence in lean/InfoGeometry/CoverageClosure.lean:201
Forbidden quarantined import: InfoGeometry.Canonical.HolographicEmergence in lean/InfoGeometry/All.lean:1288
Forbidden quarantined import: InfoGeometry.Canonical.MasterSynthesis in lean/InfoGeometry/All.lean:1473
Forbidden quarantined import: InfoGeometry.Canonical.MasterSynthesis in lean/InfoGeometry/Canonical/All.lean:1290
Forbidden quarantined import: InfoGeometry.Canonical.PositiveRayProjectiveBridge in lean/InfoGeometry/CoverageClosure.lean:246
Forbidden quarantined import: InfoGeometry.Canonical.PositiveRayProjectiveBridge in lean/InfoGeometry/All.lean:1651
Forbidden quarantined import: InfoGeometry.Canonical.RedLine in lean/InfoGeometry/All.lean:1770
Forbidden quarantined import: InfoGeometry.Canonical.Rosetta in lean/InfoGeometry/All.lean:1809
Forbidden quarantined import: InfoGeometry.Canonical.SUSYBayes in lean/InfoGeometry/All.lean:1821
Forbidden quarantined import: InfoGeometry.Canonical.SUSYBayes in lean/InfoGeometry/CoverageClosure.lean:267
Forbidden quarantined import: InfoGeometry.Canonical.WilsonLoop in lean/InfoGeometry/All.lean:2166
Forbidden quarantined import: InfoGeometry.Prequantum.Connection in lean/InfoGeometry/All.lean:3840
Forbidden quarantined import: InfoGeometry.Prequantum.Connection in lean/InfoGeometry/CoverageClosure.lean:527
Forbidden quarantined import: InfoGeometry.Prequantum.Quotient in lean/InfoGeometry/All.lean:3846
Forbidden quarantined import: InfoGeometry.Prequantum.Quotient in lean/InfoGeometry/CoverageClosure.lean:528
Forbidden quarantined import: InfoGeometry.Projective.TwistorBridge in lean/InfoGeometry/All.lean:3989
Forbidden quarantined import: InfoGeometry.Projective.TwistorBridge in lean/InfoGeometry/CoverageClosure.lean:556
Forbidden quarantined import: InfoGeometry.Unstable.YangMillsBridge in lean/InfoGeometry/CoverageClosure.lean:650
Forbidden quarantined import: InfoGeometry.Unstable.YangMillsBridge in lean/InfoGeometry/All.lean:4445
Forbidden quarantined import: InfoGeometry.Canonical.ChiralTorsionRelativeVolume in lean/InfoGeometry/CoverageClosure.lean:119
Forbidden quarantined import: InfoGeometry.Canonical.ChiralTorsionRelativeVolume in lean/InfoGeometry/All.lean:859
Forbidden quarantined import: InfoGeometry.Exploration.Symphony.Basic in lean/InfoGeometry/All.lean:2549
Forbidden quarantined import: InfoGeometry.Exploration.Symphony.Basic in lean/InfoGeometry/CoverageClosure.lean:417
Forbidden quarantined import: InfoGeometry.Exploration.Symphony.Draft in lean/InfoGeometry/CoverageClosure.lean:418
Forbidden quarantined import: InfoGeometry.Exploration.Symphony.Draft in lean/InfoGeometry/All.lean:2550
Quarantine import boundary check failed.
```

## Exact Constructivity Audit

```text
wrote /tmp/proof_gap_report.md (32 gaps)
wrote /tmp/proof_gap_report.tex
```

## Review-Only Surrogate Audit

```text
wrote /tmp/proof_gap_report.review.md (32 gaps)
wrote /tmp/proof_gap_report.review.tex
```

## Mathless Proposition Audit

```text
Found 3017 candidate(s):

lean/InfoGeometry/Algebra/AiStudioNativeMathlibFindings.lean:115: theorem scalarDisc_chiral_split [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/AiStudioNativeMathlibFindings.lean:185: theorem native_charPoly2x2_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/AnyonFiniteSpinBraid/AnyonB3ConcreteSpin.lean:32: theorem b3SpinSigma_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/AnyonFiniteSpinBraid/AnyonB3ConcreteSpin.lean:36: theorem b3SpinSigma_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/AnyonFiniteSpinBraid/AnyonLocalDefectSteps.lean:52: theorem canonical_create_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/AnyonFiniteSpinBraid.lean:122: theorem canonical_create_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/AnyonFiniteSpinBraid.lean:126: theorem canonical_annihilate_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/AnyonFiniteSpinBraid.lean:196: theorem b3SpinSigma_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/AnyonFiniteSpinBraid.lean:200: theorem b3SpinSigma_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/BaezF4H3Zorn.lean:129: theorem neg_mul_candidate [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/BaezF4H3Zorn.lean:133: theorem mul_neg_candidate [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/BaezF4H3Zorn.lean:183: theorem mem_H3ZornF4Derivations_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/BaezF4H3Zorn.lean:202: theorem H3ZornF4Derivations_eq_native [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/BerezinianPfaffianBott.lean:122: theorem det_exp_tri_facet_base [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/BostConnesAnalytic.lean:97: theorem summable_nat_rpow_neg [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/Cl11Fermions.lean:26: theorem orth [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/Cl11OSp12.lean:36: theorem e [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/ConfabulationToyModelsPart2.lean:39: theorem spatial_parity_preserves_trace [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/CubicJordanFreudenthal.lean:72: theorem adjointQuad_polarization [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/CubicJordanOs.lean:128: lemma smul_z [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/CubicJordanOs.lean:130: lemma subZ_zeroZ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/CubicJordanOs.lean:133: lemma conjZ_zeroZ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/CubicJordanOs.lean:141: lemma detZ_zeroZ_cast [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/CuntzCantorSupergradedBridge.lean:56: theorem oddStep_parity [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/CuntzCantorSupergradedBridge.lean:67: theorem wordParityZ2_append [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/CuntzChiralMomentum.lean:154: theorem diagonal_sum_eq_sum_projectors_add_n [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/CuntzChiralMomentum.lean:217: theorem central_charge_one_commutes [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/CuntzConditionalExpectation.lean:71: theorem expectation_projector [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/CuntzLorentzPoincarePresentation.lean:81: theorem majoranaSupercharge_even_of_label_false [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/CuntzLorentzPoincarePresentation.lean:252: theorem map_anticommutator [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/CuntzLorentzPoincarePresentation.lean:257: theorem map_superMomentum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/CuntzMatrixUnits.lean:35: theorem matrix_unit_star [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/CuntzMatrixUnits.lean:40: theorem matrix_unit_diag_eq_projector [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/CuntzQuotientDiracBridge.lean:50: theorem quotient_range_projector_eq_primon_P [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/CuntzSupergradedSUSY.lean:203: theorem star_cuntzMajoranaSupercharge [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/CuntzSupergradedSUSY.lean:208: theorem parity_cuntzMajoranaSupercharge [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/CuntzSupergradedSUSY.lean:225: theorem parity_cuntzCentralCharge [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/CuntzTensorQuotient.lean:205: theorem cuntz_isometry [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/CuntzTensorQuotient.lean:210: theorem cuntz_distinct_orthogonal [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/CuntzTensorQuotient.lean:294: theorem cuntz_range_projector_star [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/CuntzTraceSocketConjugation.lean:142: theorem conj_preserves_inv_pair [proof_hole]
  - contains `sorry`/`admit`

lean/InfoGeometry/Algebra/CuntzTraceSocketConjugation.lean:150: theorem isDivergence_conj_socket [proof_hole]
  - contains `sorry`/`admit`

lean/InfoGeometry/Algebra/CuntzTraceSocketConjugation.lean:178: theorem opConj_socket_trace_conserved [proof_hole]
  - contains `sorry`/`admit`

lean/InfoGeometry/Algebra/CuntzTraceSocketConjugation.lean:186: theorem opConj_logPotential_invariant [proof_hole]
  - contains `sorry`/`admit`

lean/InfoGeometry/Algebra/Det2.lean:12: theorem det2_identity [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/Det2.lean:13: theorem det2_duplicate_rows_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/Det2.lean:14: theorem det2_duplicate_cols_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/Det2.lean:15: theorem det2_swap_rows [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/Det2.lean:16: theorem det2_swap_cols [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/Det2.lean:17: theorem det2_row1_add [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/Det2.lean:18: theorem det2_row2_add [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/Det2.lean:19: theorem det2_col1_add [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/Det2.lean:20: theorem det2_col2_add [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/Det2.lean:21: theorem det2_row1_smul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/Det2.lean:22: theorem det2_row2_smul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/Det2.lean:23: theorem det2_col1_smul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/Det2.lean:24: theorem det2_col2_smul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/Det2.lean:25: theorem det2_upper_triangular [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/Det2.lean:26: theorem det2_lower_triangular [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/DirectLimitSuperClosureLemmas.lean:391: theorem directLimitLift_of [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/FibonacciGrothendieckRing.lean:94: theorem tau_snd [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/FibonacciGrothendieckRing.lean:133: theorem eval_tau [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/FibonacciGrothendieckRing.lean:180: theorem k0ToModel_tau [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/FibonacciGrothendieckRing.lean:203: theorem tensorTauRaw_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/FibonacciGrothendieckRing.lean:216: theorem tensorTauK0_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/FiniteInductiveSUSY.lean:27: theorem map_anticomm [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/FiniteInfiniteModeBridge.lean:313: theorem affine_bracket_eq_loop_bracket_plus_cocycle [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/FiniteN2Induction.lean:59: theorem map_anticommutator [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/FiniteN2Induction.lean:124: theorem iterateEnd_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/FiniteSUSYBlocks.lean:105: theorem canonical_odd_anticommutator_is_even_sum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/FinsuppN2ModeInduction.lean:45: theorem anticommutatorMode_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/FinsuppN2ModeInduction.lean:79: theorem iterateModeFamily_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/FormalSeriesCalculus.lean:27: theorem coeff_formalGeometric [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/FractalScaleTransport.lean:45: theorem iter_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/GellMannBridge.lean:20: theorem gellMann1_eq_gl1 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/GellMannBridge.lean:21: theorem gellMann2_eq_gl2 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/Grothendieck.lean:202: theorem grothendieckLift_comp [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/Grothendieck.lean:334: theorem grothendieckFunctor_mk [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/H3ZornJordanIdentity.lean:105: theorem candidateJordanMul_add_left [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/H3ZornJordanIdentity.lean:124: theorem candidateJordanMul_smul_left [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/H3ZornJordanIdentity.lean:194: theorem H3ZornJordanIdentityTarget_iff_product_law [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/H3ZornJordanProduct.lean:16: theorem H3ZornJordanProductLawAt_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/H3ZornQuadraticCommutation.lean:19: theorem tr_sub [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/H3ZornQuadraticRepresentation.lean:31: theorem linearTrace_sub [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/HypercomplexTriadMatrix.lean:48: theorem I_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/HypercomplexTriadMatrix.lean:61: theorem E_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/HypercomplexTriadMatrix.lean:74: theorem N_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/InductiveSuperClosureLemmas.lean:22: theorem map_anticommutator [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/InfiniteN2ModeInduction.lean:56: theorem iterateModeFamily_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/InfiniteN2ModeInduction.lean:208: theorem finsuppAnticommutator_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/InfiniteN2ModeInduction.lean:251: theorem iterateFinsuppModeFamily_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/InvariantTransport.lean:39: theorem square_zero_transport [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/InvariantTransport.lean:50: theorem idempotent_transport [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/InvariantTransport.lean:61: theorem involution_transport [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/InvariantTransport.lean:72: theorem commutator_transport [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/InvariantTransport.lean:82: theorem anticommutator_transport [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/InvariantTransport.lean:152: theorem central_commutes_on_image_transport [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/IterativeExponentiation.lean:33: theorem inductivePower_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/IterativeExponentiation.lean:81: theorem iterativeProduct_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/IterativeExponentiation.lean:124: theorem iterativeOrbit_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/JordanCayleyInversionHs.lean:54: theorem fundamental_identity [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/JordanCayleyInversionOs.lean:68: theorem zornNorm [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/JordanCayleyInversionOs.lean:98: theorem det_eq_quadratic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/JordanCayleyInversionOsQ.lean:114: theorem det_eq_quadratic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/JordanGradedWeight.lean:77: theorem weight_decomposition_xp [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/JordanGradedWeight.lean:82: theorem weight_decomposition_xm [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/JordanGradedWeight.lean:87: theorem weight_decomposition_z [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/K0FibonacciRing.lean:45: theorem one_a [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/K0FibonacciRing.lean:46: theorem one_b [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/K0FibonacciRing.lean:47: theorem tau_a [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/K0FibonacciRing.lean:48: theorem tau_b [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/K0FibonacciRing.lean:49: theorem add_a [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/K0FibonacciRing.lean:50: theorem add_b [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/K0FibonacciRing.lean:51: theorem mul_a [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/K0FibonacciRing.lean:52: theorem mul_b [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/KingdonAlgebra.lean:171: theorem scalar_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/KingdonAlgebra.lean:243: theorem associator_swap12_native [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/KingdonHypebasis.lean:38: theorem hypeL_eq_sub [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/KingdonSplitOctonion.lean:376: theorem scale_coeff_add [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/KingdonSplitOctonion.lean:380: theorem add_smul_abstract [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/KingdonSplitOctonion.lean:437: theorem smul_upper [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/KingdonSplitOctonion.lean:441: theorem smul_lower [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/KingdonSplitOctonion.lean:2520: theorem normalForm_add [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/KingdonSplitOctonion.lean:2524: theorem normalForm_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/KingdonSplitOctonion.lean:2528: theorem normalForm_neg [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/KleinSpinorOrbit.lean:380: theorem stabilizes_generic_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/KleinSpinorOrbit.lean:385: theorem stabilizes_null_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/KleinSpinorOrbit.lean:390: theorem stabilizes_diagonalNull_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/KleinSpinorOrbit.lean:477: theorem eq_5_23_null_Ebar_family_stabilizes [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/LorentzBiquaternionEquivalence.lean:60: theorem exactBoostTransport_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/LorentzBiquaternionEquivalence.lean:71: theorem central_sign_transport_trivial [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/NonAssocDerivation.lean:60: theorem lie_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/NonCommutativeIsometry.lean:44: theorem branch_commutator_eq_range_sub_source [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/OSp12BulkBoundaryBridge.lean:34: theorem activeSupportProjector_eq_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/OrbitClassificationBridge.lean:42: theorem zeroHerm2x2Cs_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/PauliQuaternionSplitComparison.lean:88: theorem quaternion_commutator_packet [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/PauliQuaternionSplitComparison.lean:115: theorem split_quaternion_commutator_packet [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/QuadraticJordanH3Zorn.lean:175: theorem add_readback [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/QuadraticJordanH3Zorn.lean:181: theorem neg_readback [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/QuadraticJordanH3Zorn.lean:186: theorem sub_readback [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/QuadraticJordanH3Zorn.lean:193: theorem smul_readback [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/ScaleCocycleInvariant.lean:37: theorem iter_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/SpinCore.lean:25: theorem j_plus_nilpotent [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/SplitE88Group.lean:33: theorem E8_adjoint_branches_to_D8 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/SplitOctonionIsomorphism.lean:44: theorem norm_preserved [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/SplitOctonionIsomorphism.lean:49: theorem norm_eq_detZ_cast [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/SplitQuaternionAutomorphismStructure.lean:67: theorem adj2_apply11 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/StructureConstants.lean:343: theorem f_antisym_omega [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/StructureConstants.lean:347: theorem f_cyclic_omega [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/SuperTraceBerezinian.lean:103: theorem supertrace_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/SuperTraceBerezinian.lean:106: theorem supertrace_neg [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/SuperTraceBerezinian.lean:126: theorem det_ungraded_diag [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/SuperTraceBerezinian.lean:129: theorem berezinian_diag [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/SupergradedBracket.lean:57: theorem map_commutator [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/SupergradedBracket.lean:62: theorem map_anticommutator [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/SupergradedCocycle.lean:85: theorem superBilin_rgen_qgen [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/TriFacetMatrixRealization.lean:25: theorem O_mul_P_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/VerlindeSMatrix.lean:45: theorem sqrt_ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/Zorn/Associator.lean:22: theorem associatorDefect_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/Zorn/Concrete.lean:206: theorem detZ_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/Zorn/G2TwoAutomorphismOrderLedger.lean:51: theorem autG2TwoOrder_eq_g2TwoOrder [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/Zorn/G2TwoAutomorphismOrderLedger.lean:55: theorem outG2TwoOrder_eq_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/Zorn/G2TwoAutomorphismOrderLedger.lean:59: theorem pgl3F3Order_eq_psl3F3Order [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/Zorn/RealSplitOctonionG2Classification.lean:60: theorem finiteAtlasG2TwoOrder_eq_lean_g2twoOrder [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/Zorn/ScalarJacobian8.lean:23: theorem det_scalarJacobianMatrix8 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/Zorn/SplitQuaternionCore.lean:150: theorem k_eq_il [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/ZornVectorMatrix.lean:45: theorem dot_eq_sum_coords [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/ZornVectorMatrix.lean:156: theorem dot_comm [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/ZornVectorMatrix.lean:195: theorem dot_neg_left [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/ZornVectorMatrix.lean:200: theorem dot_neg_right [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/ZornVectorMatrix.lean:473: theorem sub_eq_add_neg [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/ZornVectorMatrix.lean:580: theorem trace_diagonal_mul_diagonal [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebra/ZornVectorMatrix.lean:1365: theorem trace_commutatorJacobiator [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebraic/NarainOrthogonalCore.lean:66: theorem chargeSwapLinearEquiv_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebraic/NarainOrthogonalCore.lean:102: theorem chargeParityTwistLinearEquiv_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebraic/OddNilpotentOSpBridge.lean:91: theorem parityAt_zero_even [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebraic/OddNilpotentOSpBridge.lean:121: theorem squareZero_of_squareReadout_eq_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebraic/OperatorSurgery.lean:46: theorem null_idempotent [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebraic/OperatorSurgery.lean:50: theorem core_null_orthogonal [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebraic/RealModularReadout.lean:123: theorem normSq_conj [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebraic/SplitMajoranaOPEBridge.lean:44: theorem finiteDirichletWittenLocalFactor_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebraic/SplitMajoranaOPEBridge.lean:53: theorem finiteDirichletWittenCharacter_eq_prod [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebraic/SplitMajoranaOPEBridge.lean:76: theorem finitePfaffianCharacterReadout_eq_character [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebraic/SplitQuadraticForm.lean:51: theorem splitWeight_inr [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebraic/SplitQuadraticForm.lean:65: theorem splitQuadraticForm_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebraic/SplitSuperGeometry.lean:95: theorem supertrace_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Algebraic/SplitSuperGeometry.lean:346: theorem parityOp_comp_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analysis/AxiomFreeGNS.lean:105: theorem omega_emptyWord [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analysis/AxiomFreeGNS.lean:108: theorem omega_of_head_plus [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analysis/BregmanAnalyticBound.lean:120: theorem dikinOmegaStar_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analysis/BregmanAnalyticBound.lean:239: theorem modularExponential_isSelfAdjoint [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analysis/BregmanAnalyticBound.lean:271: theorem exponentialRemainder_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analysis/BregmanMonodromyFusion.lean:250: theorem hodge_monodromy_classification [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analysis/FiniteSpectralHeatMellin.lean:54: theorem heatTaylorReadout_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analysis/FiniteSpectralHeatMellin.lean:59: theorem scalarHeatTaylorPrefix_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analysis/FiniteSpectralMellinTaylor.lean:70: theorem pointwiseTaylorPrefix_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analysis/FiniteSpectralMellinTaylor.lean:77: theorem taylorMomentPrefix_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analysis/KatzSarnakDensity.lean:21: theorem w_U_eq_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analysis/KatzSarnakDensity.lean:25: theorem w_U_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analysis/KatzSarnakDensity.lean:29: theorem w_U_nonneg [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analysis/LaplaceTransform.lean:117: theorem zero_integral [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analysis/LaplaceTransform.lean:145: theorem neg [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analysis/LaplaceTransform.lean:160: theorem convergent_add [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analysis/LaplaceTransform.lean:227: theorem neg [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analysis/LaplaceTransform.lean:233: theorem sub [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analysis/LaplaceTransform.lean:345: theorem comp_mul_right [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analysis/LaplaceTransform.lean:432: theorem neg [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analysis/LaplaceTransform.lean:463: theorem comp_mul_right [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analysis/LaplaceTransform.lean:590: theorem hasLaplace_neg [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analysis/LaplaceTransform.lean:596: theorem hasLaplace_sub [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analysis/LaplaceTransform.lean:660: theorem hasLaplace_comp_mul_right [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analysis/LaplaceTransform.lean:704: theorem comp_mul_right [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analysis/LaplaceTransform.lean:829: theorem neg [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analysis/LaplaceTransform.lean:835: theorem sub [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analysis/MellinZetaScaling.lean:162: theorem finite_sample_product_factor_as_multiplicative_weight [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analysis/RankOneTrace.lean:40: theorem norm_rankOne_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analysis/RankOneTrace.lean:49: theorem rankOne_eq_zero_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analysis/SpectralTaylorMellinBridge.lean:33: theorem additiveTaylor_mellin_duality [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Analytic/LogSumExp.lean:343: lemma logSumExp_deriv_eq_mean [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Application/STUOperatorBridge.lean:63: theorem drazinCore_add_nil [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/AbsoluteCapstone.lean:296: theorem pillar_symmetry_available_boolean_weyl [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/Arxiv230901382RiemannZerosSymmetry.lean:48: theorem wittenStatus_unbroken_of_index_ne_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/Arxiv230901382RiemannZerosSymmetry.lean:54: theorem wittenStatus_broken_zero_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/Arxiv230901382RiemannZerosSymmetry.lean:59: theorem wittenStatus_unbroken_equal_nonzero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/BostConnesSystem.lean:234: theorem totalPrimeFactors_prime [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/BostConnesSystem.lean:255: theorem liouville_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/CantorDiracOperator.lean:129: theorem majorana_anticomm_zero_of_ne [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/CastroThetaScalingBridge.lean:118: theorem kronecker_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/CastroThetaScalingBridge.lean:122: theorem kronecker_of_ne [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ConcreteMajorana.lean:70: theorem combined_dirac_formula [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ConcreteMajorana.lean:73: theorem trivial_majorana_dirac_square [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/GenuineBounds.lean:59: theorem grover_success_probability_lower_bound [proof_hole]
  - contains `sorry`/`admit`

lean/InfoGeometry/Arithmetic/GenuineBounds.lean:86: theorem quantum_counting_chernoff_bound [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/GenuineBounds.lean:149: theorem rosser_schoenfeld_prime_count_bound [proof_hole]
  - contains `sorry`/`admit`

lean/InfoGeometry/Arithmetic/HoradamIonCatalanSlice.lean:62: theorem binetCore_cassini_shadow [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/IdeleClassZetaSymmetry.lean:213: theorem galoisAut_on_generator_eq_arithmeticGeneratorAction [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/IdeleClassZetaSymmetry.lean:426: theorem dual_reflects_centered [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/IdeleClassZetaSymmetry.lean:433: theorem dual_fixed_iff_centeredCriticalLine [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/IdeleSouriauZetaThermodynamics.lean:121: theorem dual_fixed_iff_centeredCriticalLine [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/KudinoorWittenIndexBridge.lean:53: theorem nonzero_level_superdimension_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/KudinoorWittenIndexBridge.lean:60: theorem zero_weighted_level_eq_unweighted [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/LatticeHilbertPolyaPipeline.lean:79: theorem D_eq_Q_add_Qsharp [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/LatticeHilbertPolyaPipeline.lean:274: theorem D_eq_Q_add_Qsharp [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/LatticeHilbertPolyaPipeline.lean:434: theorem hilbertPolyaEigenparameter_im [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbertSocket/BerryKeating.lean:32: theorem criticalLine [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/MobiusFermionBosonization.lean:100: theorem exteriorProduct_eq_some_union_of_disjoint [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/MobiusFermionBosonization.lean:108: theorem exteriorProduct_eq_none_of_not_disjoint [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PhysicsRiemannHypothesisFinite.lean:39: theorem muPaper_four_square_obstruction [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PhysicsRiemannHypothesisFinite.lean:42: theorem muPaper_twelve_square_obstruction [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PhysicsRiemannHypothesisFinite.lean:55: theorem muPaper_divisor_sum_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeDistributionLaw.lean:38: theorem mem_primesUpTo_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeDistributionLaw.lean:65: theorem primeCounting_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeDistributionLaw.lean:106: theorem vonMangoldtWeight_nonneg [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeDistributionLaw.lean:111: theorem vonMangoldtWeight_apply_prime [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeExteriorGraphDirac.lean:87: theorem mem_flip_of_ne [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeExteriorGraphDirac.lean:96: theorem card_flip_of_not_mem [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeExteriorGraphDirac.lean:105: theorem card_flip_add_one_of_mem [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeExteriorGraphDirac.lean:266: theorem weightedNumberEnergy_eq_sum_occupied [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeExteriorGraphDirac.lean:297: theorem weightedNumberEnergy_primeEnergy_eq_stateEnergy [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeExteriorGraphDirac.lean:339: theorem flip_involutive [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeExteriorRepresentation.lean:132: theorem Gamma_eq_negOne_pow_fermionNumber [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeGrandCanonicalEnsemble.lean:179: theorem gibbsWeight_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeGrandCanonicalSouriauBregman.lean:110: theorem complexBosonGrandPartition_eq_prod_inv [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeGrandCanonicalSouriauBregman.lean:275: theorem finitePrimeBosonGrandPartition_eq_prod [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeGrandCanonicalSouriauBregman.lean:298: theorem finitePrimeGrandPotential_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeGrandCanonicalSouriauWeights.lean:96: theorem complexBosonGrandPartition_eq_prod_inv [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeGrandCanonicalSouriauWeights.lean:132: theorem grandPotential_eq_neg_inv_beta_mul_massieu [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeGrandCanonicalSouriauWeights.lean:169: theorem finitePrimeBosonGrandPartition_eq_prod [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeMajoranaBitFlip.lean:90: theorem card_majoranaFlip_of_not_mem [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeMajoranaCAR.lean:30: theorem map_anticomm [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeMajoranaCAR.lean:103: theorem ringEquiv_anticomm [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeMajoranaCAR.lean:169: theorem ringHom_preserves_square_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeMajoranaCAR.lean:176: theorem ringHom_preserves_idempotent [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeMajoranaCAR.lean:183: theorem ringHom_preserves_involution [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeMajoranaCAR.lean:195: theorem ringHom_preserves_anticommutator_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeMajoranaCAR.lean:206: theorem ringHom_preserves_anticommutator_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeMajoranaCAR.lean:217: theorem ringHom_preserves_commutator_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeMajoranaCAR.lean:224: theorem ringHom_preserves_commutator_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeMajoranaCAR.lean:278: theorem eps_iota_add_iota_eps [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeMajoranaLocalMode.lean:121: theorem epsilon_iota_anticomm' [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeMajoranaLocalMode.lean:126: theorem iota_epsilon_anticomm' [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeMajoranaWittenCharacter.lean:115: theorem finiteWittenCharacter_eq_mobiusGradedThermalCharacter [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeParafermionGrandCanonicalClock.lean:150: theorem finiteParafermionLocalFactor_three [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeParafermionGrandCanonicalClock.lean:211: theorem finiteGrandParafermion3Partition_empty [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeParafermionGrandCanonicalClock.lean:285: theorem grandComplexPrimeWeight_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeParafermionGrandCanonicalClock.lean:335: theorem grandCanonicalSurprisal_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeParafermionGrandCanonicalClock.lean:351: theorem shannonEntropyFromSurprisal_eq_expectedSurprisal [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeParafermionRecurrence.lean:14: theorem finiteParafermionLocalFactor_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeParafermionRecurrence.lean:26: theorem finiteGrandParafermionPartition_insert [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeSpinorSquareRootBoost.lean:71: theorem diracCoefficient_sq_eq_energyFromCoefficient [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeSpinorWittenIndex/Pfaffian.lean:27: theorem majoranaBlockPfaffian_sq_eq_determinant [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeSuperalgebra.lean:247: theorem finiteComplexBosonPartition_empty [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeSuperalgebra.lean:340: theorem infiniteComplexParafermionZetaRatio_two_eq_positiveFermion [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeSupertraceFinite.lean:94: theorem paritySign_empty [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeWeylDenominatorBridge.lean:67: theorem finitePrimeWeylDenominator_eq_signedFermionPartition [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimeWeylDenominatorBridge.lean:76: theorem finitePrimeBosonicInverseDenominator_eq_bosonPartition [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimitivePrimeProjectiveTemperature.lean:49: theorem arithmeticPrimeRestrictedPartition_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimitivePrimeProjectiveTemperature.lean:56: theorem arithmeticPrimeInvertedPartitionDensity_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean:259: theorem PrimitiveFinset_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean:265: theorem SupportedAboveFinset_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean:271: theorem primitiveWeight_eq_zero_of_not_lt_two [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean:300: theorem realVonMangoldt_eq_if_isPrimePow [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean:304: theorem realVonMangoldt_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean:313: theorem realVonMangoldt_eq_zero_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean:317: theorem realVonMangoldt_ne_zero_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean:321: theorem realVonMangoldt_pos_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean:325: theorem realVonMangoldt_apply_pow [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean:329: theorem realVonMangoldt_apply_prime [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean:333: theorem sum_realVonMangoldt_divisors [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean:355: theorem primitiveModularKernel_eq_mellinKernel_shift [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean:480: theorem log_nat_pos_of_two_le [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean:541: theorem primitiveWeight_mul_eq_of_right_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean:668: theorem primitiveWeightSum_empty [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean:672: theorem primitiveWeightSum_singleton [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean:676: theorem arithmeticCountWeight_eq_mul_kernel [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean:680: theorem arithmeticPartition_eq_sum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean:684: theorem arithmeticTotalMass_eq_sum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean:688: theorem arithmeticBaseShape_eq_div [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean:889: theorem arithmeticShapeMellin_eq_sum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean:894: theorem arithmeticPartition_empty [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean:898: theorem arithmeticTotalMass_empty [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean:902: theorem arithmeticShapeMellin_empty [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean:906: theorem arithmeticPrimePartition_eq_sum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean:911: theorem arithmeticPrimePartition_empty [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean:1250: theorem primitiveDivisorFiber_eq_filter [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimitiveSetsAbove.lean:1254: theorem primitiveDivisorQuotient_eq_image_fiber [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimitiveSouriauZeta.lean:62: theorem primitiveFiniteZetaPartition_eq_arithmeticPartition_unit [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimonFreeEnergyRelativeTrace.lean:79: theorem determinantLineInversion_involutive [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimonFreeEnergyRelativeTrace.lean:128: theorem primitiveMellinParityIdentification [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimonGasPartition.lean:126: theorem finiteBosonicMobiusEulerFactor_empty [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimonLiouvilleWittenIndex.lean:126: theorem rawHyperbolicChiralIndex_eq_stable_sub_unstable [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimonMajoranaWittenCharacter.lean:83: theorem finiteWittenCharacter_empty [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimonMajoranaWittenCharacter.lean:87: theorem finiteWittenCharacter_insert [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimonMajoranaWittenCharacter.lean:260: theorem pfaffian_majoranaPfaffianBlock [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimonSupergradedGasAlgebra.lean:123: theorem finitePrimonWittenIndex_cancel [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimonThermodynamics.lean:70: theorem bosonPartition_singleton [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimonThermodynamics.lean:74: theorem fermionPartition_singleton [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/PrimonThermodynamics.lean:79: theorem bosonPartition_union [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ProjectivePrimePartition.lean:35: theorem projectivePrimePartition_eq_restricted [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ProjectiveWeylGauge.lean:40: theorem projectiveWeylThermalMass_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ProjectiveWeylGauge.lean:47: theorem projectiveArithmeticShape_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/QuasicrystalRHExplicitFormula.lean:50: theorem lambdaR_ne_zero_iff_primePowerAtom [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/QuasicrystalRHExplicitFormula.lean:55: theorem lambdaR_eq_zero_iff_not_primePowerAtom [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/QuasicrystalRHExplicitFormula.lean:60: theorem lambdaR_apply_prime [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/QuasicrystalRHExplicitFormula.lean:66: theorem lambdaR_apply_pow [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/QuasicrystalRHExplicitFormula.lean:72: theorem sum_lambdaR_divisors [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/RamanujanDefectTower.lean:51: theorem dirichletChannelSplit_product [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/RamanujanOddZeta.lean:130: theorem reflectedModularWeight_eq_sign_factored [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/RamanujanOddZeta.lean:140: theorem ramanujanOddZetaLHS_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/RiemannZetaEquivalences.lean:166: theorem eulerProductZeta_eq_riemannZeta [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/SelfConcordantZetaBarrier.lean:83: theorem bregman_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/SplitCliffordRealization.lean:61: theorem euler_anticommutes_J [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/SplitMajoranaLocal.lean:257: theorem holeNumberOp_add_numberOp_eq_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/SplitMajoranaPrimon.lean:90: theorem occupationInt_of_notMem [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/SplitMajoranaPrimon.lean:94: theorem localMajoranaParity_of_mem [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/SplitMajoranaPrimon.lean:98: theorem localMajoranaParity_of_notMem [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/SplitMajoranaPrimon.lean:210: theorem localSpinorPairing_eq_eulerFactor [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/TrifactorZetaBridge.lean:83: theorem centeredXi_zero_reflected [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaChiralConeProjection.lean:42: theorem conjugation_criticalMirror_eq_functionalDual [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaCoordinateSymmetry.lean:148: theorem chartCriticalLine_iff_complexCriticalLine [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaCoordinateSymmetry.lean:165: theorem centeredSigma_chartConjugation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaCoordinateSymmetry.lean:504: theorem criticalTangent_idempotent [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaCoordinateSymmetry.lean:509: theorem criticalNormal_idempotent [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaCoordinateSymmetry.lean:514: theorem criticalNormal_after_tangent [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaCoordinateSymmetry.lean:519: theorem criticalTangent_after_normal [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaCoordinateSymmetry.lean:535: theorem conjugation_preserves_flatQuadratic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaCoordinateSymmetry.lean:540: theorem functionalDual_preserves_flatQuadratic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaCoordinateSymmetry.lean:545: theorem criticalMirror_preserves_flatQuadratic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaCoordinateSymmetry.lean:565: theorem invariantPotential_opposite_normal_values [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaCoordinateSymmetry.lean:606: theorem normalQuadraticPotential_criticalMirror [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaCoordinateSymmetry.lean:611: theorem normalQuadraticPotential_eq_zero_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaCoordinateSymmetry.lean:620: theorem heightTranslation_preserves_u [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaCoordinateSymmetry.lean:630: theorem criticalMirror_commutes_heightTranslation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaCoordinateSymmetry.lean:639: theorem heightTranslation_preserves_flatDisplacement [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaCoordinateSymmetry.lean:673: theorem heightSouriauMoment_equivariance [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaCoordinateSymmetry.lean:679: theorem normalQuadraticPotential_heightTranslation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaCoordinateSymmetry.lean:866: theorem discreteZetaSouriauMoment_invariant [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaCoordinateSymmetry.lean:873: theorem discreteZetaMassieu_invariant [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaDihedral.lean:42: theorem tau_involution [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaDihedral.lean:46: theorem sigma_involution [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaDihedral.lean:50: theorem gamma_involution [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaDihedral.lean:54: theorem tau_sigma_commute [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaKANDirichletFactorization.lean:92: theorem scalarKANDirichletProduct_of_criticalLine [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaPrimeFluctuationBridge.lean:63: theorem normalProjection_u [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaPrimeFluctuationBridge.lean:67: theorem normalProjection_v [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaPrimeFluctuationBridge.lean:71: theorem tangentProjection_u [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaPrimeFluctuationBridge.lean:75: theorem tangentProjection_v [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaSouriauComplexLift.lean:820: theorem finitePrimeBosonPartition_eq_prod [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaSouriauThermodynamics.lean:247: theorem grandPotential_eq_neg_inv_beta_mul_massieu [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaSouriauThermodynamics.lean:563: theorem finitePrimeBosonGrandPartition_eq_prod [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaSymmetryAdaptedDefinitions.lean:142: theorem centeredDirichletMode_conjugation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaSymmetryAdaptedDefinitions.lean:148: theorem centeredDirichletMode_functionalDual [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaSymmetryAdaptedDefinitions.lean:154: theorem centeredDirichletMode_criticalMirror [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaSymmetryAdaptedDefinitions.lean:189: theorem finiteDirichletReadout_insert [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaTraceSpecialization.lean:104: theorem finitePrimeGasPartition_eq_denominator_inv [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaTraceVielbeinSpecialization.lean:76: theorem primeLocalEffectiveAction_def [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaTraceVielbeinSpecialization.lean:147: theorem canonicalPrimeVielbein_eulerSupervolume [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaTraceVielbeinSpecialization.lean:153: theorem canonicalPrimeVielbein_traceLogSupervolume_eq_riemannZeta [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Arithmetic/ZetaTraceVielbeinSpecialization.lean:159: theorem canonicalPrimeVielbein_eulerSupervolume_eq_riemannZeta [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Audit.lean:6: def printDebt [proof_hole]
  - contains `sorry`/`admit`

lean/InfoGeometry/Automath/Generated/cuntz_fibonacci_resolvent.lean:12: theorem cuntz_fibonacci_resolvent [proof_hole]
  - contains `sorry`/`admit`

lean/InfoGeometry/Automath/Generated/cuntz_shift_commutativity.lean:12: theorem cuntz_shift_commutativity [proof_hole]
  - contains `sorry`/`admit`

lean/InfoGeometry/Automath/Generated/cuntz_yang_baxter.lean:12: theorem hypothesis4_yang_baxter_relation [proof_hole]
  - contains `sorry`/`admit`

lean/InfoGeometry/Automath/Generated/hyp_1_spectral_rigidity.lean:12: theorem hyp_1_spectral_rigidity [proof_hole]
  - contains `sorry`/`admit`

lean/InfoGeometry/Automath/Generated/hyp_2_fibonacci_functional_calculus.lean:12: theorem hyp_2_fibonacci_functional_calculus [proof_hole]
  - contains `sorry`/`admit`

lean/InfoGeometry/Automath/Generated/hyp_3_operator_roots.lean:12: theorem hyp_3_operator_roots [proof_hole]
  - contains `sorry`/`admit`

lean/InfoGeometry/Automath/Generated/hyp_4_braid_image.lean:8: theorem hyp_4_braid_image [proof_hole]
  - contains `sorry`/`admit`

lean/InfoGeometry/Automath/Generated/hyp_5_k_theory.lean:12: theorem hyp_5_k_theory [proof_hole]
  - contains `sorry`/`admit`

lean/InfoGeometry/Automorphic/LanglandsSugawaraBridge.lean:122: theorem centralCharge_eq_projectedL_zero_of_match [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Automorphic/RoelckeSelbergSpectral.lean:377: theorem potential_eq_zero_of_abs_eq_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Automorphic/SiegelArithmeticResonanceOperator.lean:287: theorem cubicNorm_boundaryLift_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Automorphic/SiegelResonance.lean:117: theorem cuspidalProjector_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Automorphic/SiegelResonance.lean:204: theorem siegel_cuspidalProjector_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Automorphic/SiegelResonance.lean:349: theorem boundaryProjector_eisenstein [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Automorphic/SiegelResonance.lean:356: theorem cuspidalProjector_eisenstein [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Automorphic/SiegelResonance.lean:363: theorem bulk_decomposition [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Automorphic/SiegelResonance.lean:439: theorem mem_globalCuspidalSubspace_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/BostConnes/BostConnesParity.lean:20: theorem moebius_eq_liouvilleParity_of_squarefree [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/BostConnes/BostConnesParity.lean:25: theorem moebius_eq_zero_of_not_squarefree [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/BostConnes/BostConnesThermofield.lean:72: theorem modular_phase_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/AFRecursiveLimitBridge.lean:86: theorem readback_idempotent [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/AlgebraicDerivations.lean:146: theorem adLinear_lie_morphism [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/AlgebraicDerivations.lean:207: theorem omega2_is2cocycle_iff_cyclic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/AlgebraicDerivations.lean:240: theorem omega3_is3cocycle_iff_expanded [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/AlgebraicDerivations.lean:254: theorem omega3_expanded_sum_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/AmariSouriauThermodynamicGauge.lean:79: theorem bregman_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/AmariSouriauThermodynamicGauge.lean:83: theorem dualCoord_eq_grad [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/AmariSouriauThermodynamicGauge.lean:203: theorem expectation_coord_eq_grad_log_partition [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/AmariSouriauThermodynamicGauge.lean:264: theorem dual_linear_relaxation_dualCoord [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/AmariSouriauThermodynamicGauge.lean:318: theorem eta_eq_gradient_formula [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/AnomalyOwnerMap.lean:41: theorem drazin_dilation_anomaly_corridor [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Arithmetic/ZetaEulerProductBridge.lean:34: theorem finiteEulerProduct_empty [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Arithmetic/ZetaEulerProductBridge.lean:74: theorem zeta_euler_product_bridge [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/AtiyahSingerWittenIndexBridge.lean:57: theorem grading_operator_diag_physical [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/AtiyahSingerWittenIndexBridge.lean:80: theorem witten_index_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BarbarescoSPILG2020.lean:59: theorem kks_alternating [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BarbarescoSPILG2020.lean:66: theorem souriauTheta_eq_kks [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BarbarescoSPILG2020.lean:87: theorem legendreReadout_eq_zero_on_dual_line [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BayesianHodgeCurrent.lean:118: theorem protectedHarmonicCurrent_closed_coclosed [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BayesianMarkovChain.lean:183: theorem iterateState_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BayesianMarkovHodgeBridge.lean:67: theorem stationary_current_is_harmonic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Berezinian.lean:15: theorem ber_id [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Berezinian.lean:18: theorem ber_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Berezinian.lean:22: theorem ber_inv [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Berezinian.lean:26: theorem ber_eq_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BerezinianTrace.lean:35: theorem supertrace_diag [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BerezinianTrace.lean:44: theorem ber_eq_div [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BerezinianTrace.lean:47: theorem ber_eq_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BerezinianTrace.lean:51: theorem ber_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BerezinianTrace.lean:57: theorem ber_inv [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BerezinianTrace.lean:62: theorem ber_exp_eq_exp_str [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BerryPhase.lean:65: theorem informationBerryPhase_eq_loopLength_mul_chiralAnomalyIndex [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BerryPhase.lean:71: theorem informationBerryPhase_eq_loopLength_mul_epsilon_mul_rank [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BiQuaternionKahlerFinite.lean:118: theorem fisherMetric_symmetric [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BiQuaternionKahlerLegendreFinite.lean:64: theorem hamiltonian_eq_total_energy [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BiQuaternionKahlerSymplecticNoetherBridge.lean:48: theorem lagrangianSymplecticForm_eq_symplecticI [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BiQuaternionKahlerThermo.lean:59: theorem MassieuPotential_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BiquaternionDualRootRegularizer.lean:65: theorem tr2_pauliVector [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BiquaternionDualRootRegularizer.lean:116: theorem det2_N [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BiquaternionDualRootRegularizer.lean:120: theorem tr2_N [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BiquaternionDualRootRegularizer.lean:130: theorem plusBoundary_sub_I_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BiquaternionDualRootRegularizer.lean:134: theorem det2_plusBoundary_sub_I [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BiquaternionDualRootRegularizer.lean:138: theorem minusBoundary_add_I_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BiquaternionDualRootRegularizer.lean:142: theorem det2_minusBoundary_add_I [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BiquaternionLaplaceTripotent.lean:93: theorem scale_det_at_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BiquaternionLaplaceTripotent.lean:96: theorem scale_det_at_neg_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BogoliubovCartanFrameInterpretation.lean:42: theorem bogoliubovFrameAction_eq_conjugate [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BogoliubovCartanFrameInterpretation.lean:206: theorem primitive_operator_owner [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BosonizationConstructiveCurrent.lean:141: lemma central_commutes [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BosonizationConstructiveCurrent.lean:1322: theorem completedDiagonalCurrent_coeff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BosonizationConstructiveCurrent.lean:1351: theorem cutoffDiagonalCurrent_coeff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BosonizationConstructiveCurrent.lean:1386: theorem completedCurrent_coeff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BosonizationConstructiveCurrent.lean:1456: theorem formalCurrentNoncentralCoeff_eq_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BosonizationConstructiveCurrent.lean:1527: theorem completedCurrentMode_centralCoeff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BosonizationConstructiveCurrent.lean:1542: theorem centralCurrentClass_centralCoeff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BosonizationConstructiveCurrent.lean:1582: theorem completedCurrentModeBracket_centralCoeff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BosonizationConstructiveCurrent.lean:1863: theorem completedNonabelianCurrent_centralCoeff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BosonizationConstructiveCurrent.lean:1955: theorem completedNonabelianCurrentBracketFromWick_centralCoeff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BosonizationSchwinger.lean:65: theorem schwingerCocycle_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BosonizationSchwinger.lean:75: theorem schwingerCocycleCoeff_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BostConnesConformalBoundary.lean:76: theorem uncharged_sugawara_central_vacuum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BostConnesGibbsState.lean:52: theorem bostConnesExpectation_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BostConnesKMS.lean:88: theorem S_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BostConnesKMS.lean:93: theorem S_isometry [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BostConnesKMS.lean:177: theorem kmsProjectionWeight_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BostConnesKMS.lean:262: theorem kmsProjectionReadout_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BostConnesKMS.lean:304: theorem kms_evaluation_on_diagonal_projection [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BostConnesKMS.lean:310: theorem kms_evaluation_on_off_diagonal_projection [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BostConnesLiouvilleModularComm.lean:63: theorem modularPhase_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BostConnesSuperalgebra.lean:88: theorem local_boson_mul_wittenFactor [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BostConnesSuperalgebra.lean:94: theorem wittenFactor_mul_local_boson [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BoundaryMatrixUnitWick.lean:220: lemma comm_sub_zsmul_one_left [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BoundaryMatrixUnitWick.lean:224: lemma comm_sub_zsmul_one_right [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/BregmanDeformation.lean:122: theorem bregman_deformation_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CPTGradingCompass.lean:136: theorem witten_moebius_index_cancellation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CanonicalZornCliffordRepresentation.lean:51: theorem coordinateQuadratic_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CanonicalZornCliffordRepresentation.lean:181: theorem complexSpinDiracRepresentation_val [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CanonicalZornCompositionFiveGradeBridge.lean:62: theorem realVector8_val [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CanonicalZornFiveGradedClosure.lean:460: theorem conformalVectorQuadratic_pac55Coordinates [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CanonicalZornIntegralSpinRepresentation.lean:95: theorem integralSpinRepresentation_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CanonicalZornIntegralSpinTrialityClosure.lean:38: theorem realSplit44ToPAC44_integralZornToRealSplit44 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CanonicalZornOuterTrialityGroup.lean:53: theorem vectorAct_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CanonicalZornOuterTrialityGroup.lean:56: theorem spinorPlusAct_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CanonicalZornOuterTrialityGroup.lean:59: theorem spinorMinusAct_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CanonicalZornOuterTrialityGroup.lean:165: theorem transportGL_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CanonicalZornOuterTrialityGroup.lean:384: theorem axisRelatedTriple_vector_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CanonicalZornOuterTrialityGroup.lean:387: theorem axisRelatedTriple_spinorPlus_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CanonicalZornOuterTrialityGroup.lean:390: theorem axisRelatedTriple_spinorMinus_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CanonicalZornOuterTrialityGroup.lean:403: theorem zornTrace_canonicalTriality [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CanonicalZornRealSpin44.lean:178: theorem realGammaLinear_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CanonicalZornSpinRelatedFiber.lean:44: theorem relatedDiracRepresentation_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CanonicalZornSpinVectorAction.lean:618: theorem complexSpinTrialityMinusRepresentation_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CanonicalZornSpinVectorAction.lean:676: theorem trialityForm_eq_traceProductPair [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CanonicalZornTrialitySpinEquivariance.lean:232: theorem axisTransportedSpinRepresentation_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CantorBinaryHopCharge.lean:100: theorem charge_hopHead_nil [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CantorBinaryHopCharge.lean:107: theorem creation_realizes_false_hop [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CantorBoundaryCuntzShift.lean:87: theorem boundaryPrefix_prefixBit_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CantorBoundaryCuntzShift.lean:92: theorem boundaryPrefix_prefixBit_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CantorBoundaryCuntzShift.lean:201: theorem leftOperator_eq_cuntz [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CantorBoundaryCuntzShift.lean:205: theorem rightOperator_eq_cuntz [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CantorCl11Limit.lean:69: theorem prefixStageSequence_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CantorCylinderLattice.lean:157: theorem cylinder_idempotent [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CantorCylinderPrior.lean:40: theorem uniformKMSPrior_weight_nonneg [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CantorCylinderPrior.lean:44: theorem uniformKMSPrior_successor_consistent [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CantorCylinderTopology.lean:65: theorem initialSegmentSet_finite [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CantorCylinderTopology.lean:114: theorem principalUltrafilter_initialSegmentCylinder_eval [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CantorDiracSeaHopping.lean:115: theorem charge_flipAt_twice [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CantorFockSpace.lean:51: theorem localVacuum_annihilation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CantorFockSpace.lean:68: theorem local_entropyFlux_eq_annihilation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CantorModularScoreFunctional.lean:163: theorem scoreAt_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CantorModularScoreFunctional.lean:202: theorem scoreLinear_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CantorProjectiveLimit.lean:126: theorem cantorHomeomorph_projection [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CantorSplitNullBridge.lean:144: theorem addressNullGenerator_child_ne_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CantorSplitNullBridge.lean:149: theorem addressNullGenerator_child_detZ_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CantorSplitNullBridge.lean:154: theorem addressNullGenerator_child_sq_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CantorSplitNullExternalAudit.lean:110: theorem observedMacaulay2Derham0_not_verified [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CantorianFractalSpacetime.lean:178: theorem mersenne_decomp_137 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CantorianFractalSpacetime.lean:182: theorem binary_expansion_137 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CayleyCriticalLineCircleBridge.lean:126: theorem cayleyToFugacity_mem_unitCircle_iff_criticalLine [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CayleyMobiusBoundaryBraidClosure.lean:63: theorem not_isInterior_boundary [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CayleyMobiusPowerLaws.lean:24: theorem inversion_iterate_two [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CayleyMobiusPowerLaws.lean:61: theorem reflection_iterate_even [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CayleyMobiusPowerLaws.lean:65: theorem reflection_iterate_odd [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CelikErlangenBraidBridge.lean:150: theorem braid_generator_from_pauli [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CelikKocakPaperFormalism.lean:531: theorem cl11PauliMatrixEquiv_map_e1 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CelikKocakPaperFormalism.lean:537: theorem cl11PauliMatrixEquiv_map_e2 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean:110: theorem chiralScale_eq_zero_iff_chiralAnomaly_eq_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CertifiedInverseKernel.lean:115: theorem rightChiralAnomaly_eq_chiralAnomaly_of_projectorAgreement [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ChiralCausalConeFlow.lean:53: lemma rindler_boost_t [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ChiralCausalConeFlow.lean:58: lemma rindler_boost_z [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ChiralCausalConeFlow.lean:87: theorem weyl_trace_scaling [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ChiralKKTIsolation.lean:322: theorem zeroModePfaffian_square_eq_determinantShadow [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ChiralNullSpaceBridge.lean:43: theorem excitedStateSector_eq_orthogonal [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ChiralNullSpaceBridge.lean:47: theorem regulatedHeatKernel_eq_subtract_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ChiralRadiationCones.lean:44: theorem constructive_mass_eq_flipRate [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ChiralSuperPoincareSouriauBridge.lean:43: theorem minkowskiMetricCoeff_time_time [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ChiralSuperPoincareSouriauBridge.lean:47: theorem minkowskiMetricCoeff_space_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ChiralSuperPoincareSouriauBridge.lean:51: theorem minkowskiMetricCoeff_off_diag [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ChiralSuperPoincareSouriauBridge.lean:63: theorem betaProjectedEnergy_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ChiralSuperPoincareSouriauBridge.lean:224: theorem betaEnergy_eq_minkowski_pair [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Cl11TensorTowerBridge.lean:27: theorem det_stageEmbed [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Cl11TensorTowerBridge.lean:32: theorem normalizedTrace_stageEmbed [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Cl11TensorTowerBridge.lean:37: theorem normalizedLogAbsDet_stageEmbed [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Cl3ComplexMatrixProduct.lean:429: lemma finrank_prodMat2C [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Cl55V4SpinorFragmentation.lean:32: theorem J_sandwich_u [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Cl55V4SpinorFragmentation.lean:36: theorem J_sandwich_v [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Cl55V4SpinorFragmentation.lean:40: theorem S_sandwich_u [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Cl55V4SpinorFragmentation.lean:44: theorem S_sandwich_v [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CliffordDiracAlgebra.lean:74: theorem Pplus_add_Pminus [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CliffordEquiv.lean:338: theorem peirceCliffordEquivalence_eq_trans [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CliffordEquiv.lean:345: theorem peirceLadder_J_eq_cl11_generator [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CliffordO55ProjectiveReconciliation.lean:52: theorem cl55_window_is_stage_five [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CliffordO55ProjectiveReconciliation.lean:73: theorem cl55_tensor_step_eq_owner [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CliffordO55ProjectiveReconciliation.lean:84: theorem cl44_spinorMatrix4_basis_compatibility [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CoarseGraining.lean:35: theorem totalWeight_eq_sum_fiberWeight [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ComplexCliffordHierarchy.lean:70: theorem shape_add_two [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ComplexCliffordHierarchy.lean:75: theorem shape_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ComplexCliffordHierarchy.lean:76: theorem shape_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ComplexCliffordHierarchy.lean:77: theorem shape_two [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ComplexCliffordHierarchy.lean:78: theorem shape_three [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ComplexCliffordHierarchy.lean:79: theorem shape_four [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ComplexCliffordHierarchy.lean:80: theorem shape_five [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ComplexCliffordHierarchy.lean:81: theorem shape_six [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ComplexCliffordHierarchy.lean:82: theorem shape_seven [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ComplexCliffordHierarchy.lean:83: theorem shape_eight [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ComplexModularFlow.lean:36: theorem zero_beta_cos [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ComplexModularFlow.lean:41: theorem zero_beta_sin [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ComplexModularFlow.lean:113: theorem expBregman_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ConformalAlgebra.lean:105: theorem generatorCartanDecomposition_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ConformalAnomalySource.lean:208: theorem obstructionScale_eq_projectorObstruction_nnnorm [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ConformalAnomalySource.lean:213: theorem projectorObstruction_nnnorm_eq_obstructionScale [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ConformalAnomalySource.lean:218: theorem chiralScale_eq_obstructionScale [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ConformalAnomalySource.lean:223: theorem epsilon_eq_obstructionScale [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ConformalAnomalySource.lean:264: theorem projectorObstructionSquashCoeff_eq_squashedObstructionScale_div_obstructionScale [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ConformalAnomalySource.lean:1161: theorem unitOfAction_eq_obstructionScale [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ConformalFiveGradeInversion.lean:106: theorem fixed_negTwo_mem_posTwo [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ConformalFiveGradeInversion.lean:115: theorem fixed_posTwo_mem_negTwo [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ConformalFiveGradeInversion.lean:124: theorem fixed_negOne_mem_posOne [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ConformalFiveGradeInversion.lean:133: theorem fixed_posOne_mem_negOne [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ConformalProjectorCore.lean:428: theorem specialConformal_eq_modularInversion_translation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ConformalProjectorCore.lean:463: theorem dilation_eq_half_sub_mp_projectors [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ConformalProjectorCore.lean:672: theorem singularEinsteinAnomaly_eq_neg_rightChiralAnomaly [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ConformalProjectorCore.lean:816: theorem rightProjector_commute_of_projectorAgreement_of_metricProjector_commute [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ConformalProjectorCore.lean:905: theorem chiral_commutation_link [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ConformalProjectorCore.lean:912: theorem chiralAnomalyOperator_eq_zero_iff_projectors_commute [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ConformalProjectorCore.lean:919: theorem leftChiralAnomalyOperator_eq_zero_iff_projectors_commute [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ConnesRadonNikodymCocycle.lean:101: theorem cocycleDerivative_eq_hamiltonian_diff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CoproductToVirasoroCocycleBridge.lean:589: theorem modularAutomorphism_beta_polynomial [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CoproductToVirasoroCocycleBridge.lean:680: lemma vacuumExpectation_zero_of_observable_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CoproductToVirasoroCocycleBridge.lean:712: lemma vacuumExpectation_sum_of_zero_actions [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CoproductToVirasoroCocycleBridge.lean:956: theorem iteratedVirasoroCocycle_two_resonant_eq_lgen_snd [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CreationAnnihilationTomitaBridge.lean:74: theorem J_evenMajorana [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CreationAnnihilationTomitaBridge.lean:79: theorem J_oddDensity [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CuntzCantorBoundaryShift.lean:71: theorem prependBit_head [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CuntzCliffordBottBridge.lean:58: theorem clockStageSequence_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CuntzCrystalRepresentation.lean:13: theorem raiseLeft_lowerRight [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CuntzCrystalRepresentation.lean:18: theorem raiseRight_lowerLeft [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CuntzSuperBraidMoEBridge.lean:75: theorem central_generator_particle_to_hole [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CuntzSuperBraidMoEBridge.lean:80: theorem central_generator_hole_to_particle [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CuntzSuperBraidMoEBridge.lean:128: theorem particle_strand_parity [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CuntzTomitaTakesaki.lean:162: theorem DeltaHalf_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CuntzTomitaTakesaki.lean:167: theorem modularJ_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CurrentConjugationLemmas.lean:31: theorem conjugateEnd_commutator [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CurrentConjugationLemmas.lean:72: theorem currentSugawara_lgen_conjugated [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/CurrentConjugationLemmas.lean:87: theorem currentSugawara_cgen_conjugated [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/DeRhamBoltzmannModular.lean:23: theorem entropyPotential_wellDefined [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/DeformedIdeleActionBridge.lean:54: theorem branchProjection_idempotent [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/DeformedSuperCuntzWarp.lean:201: theorem deficitAngle_eq_zero_of_angle_sums_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/DeformedSuperCuntzWarp.lean:242: theorem boson_even [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/DeformedSuperCuntzWarp.lean:245: theorem fermion_odd [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/DiracSouriauOperator.lean:79: theorem toMatrix_eq_fromBlocks [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/DiscreteCPTGroup.lean:74: theorem z2T_add_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/DiscreteCPTGroup.lean:94: theorem card_CPTZ2 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/DiscreteDiracHodgeChiralBridge.lean:82: theorem dirac_square_check_K3 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/DiscreteStokesFinite.lean:65: theorem finite_stokes [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/DrazinSupercharge.lean:204: theorem drazinComplementaryProjector_mul_drazinSpectralProjector [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/DrazinSupercharge.lean:259: theorem commutator_drazinSpectralProjector_drazinDilationGap_eq_half_sub_anomalies [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/DrazinSupercharge.lean:397: theorem supercharge_is_oddK [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/DunfordTaylor.lean:76: theorem mem_resolventSet_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/DunfordTaylor.lean:134: theorem dunfordTaylorIntegral_const_contour [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/DunfordTaylor.lean:151: theorem rieszProjection_const_contour [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/EPAndGroupInverse.lean:393: theorem spectralProjector_commutator_dilationGap_eq_zero_of_dilationGap_eq_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean:164: theorem liftedRightChiralAnomalyOperator_ne_zero_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/EmergentGravity.lean:170: theorem inducedMetric_zero_vielbein [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/EmergentGravity.lean:215: theorem emergent_torsion_consistency [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/EmergentGravity.lean:221: theorem emergent_vielbein_consistency [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/EmergentGravity.lean:248: theorem contorsionFromTorsion_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/EmergentGravity.lean:275: theorem curvatureCorrection_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/EmergentGravity.lean:297: theorem effectiveActionDensity_zero_torsion [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/EmergentGravityActionVariation.lean:44: theorem effectiveActionVariation_torsion_split [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/EvansHarmonicTrap.lean:53: theorem toHodgeSector_exact [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/EvansHarmonicTrap.lean:56: theorem toHodgeSector_coexact [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/EvansHarmonicTrap.lean:59: theorem toHodgeSector_harmonic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/EvansHarmonicTrap.lean:75: theorem exact_harmonic_moves_right [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/EvansHarmonicTrap.lean:80: theorem harmonic_coexact_moves_left [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/EvansHarmonicTrap.lean:85: theorem exact_coexact_swap [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/EvansHarmonicTrap.lean:93: theorem harmonic_trap_invariant_left [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/EvansHarmonicTrap.lean:131: theorem harmonic_trap_updateLeft [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/EvansHarmonicTrap.lean:135: theorem harmonic_trap_updateRight [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FenchelExpLogScalar.lean:110: theorem bregmanPrimal_closed [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FenchelExpLogScalar.lean:171: theorem bregmanDual_closed [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FibonacciGrothendieckLimitBridge.lean:45: theorem fibFusionTensorTau_model_mul_tau [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FibonacciParafermionAtoms.lean:268: theorem z3_R_B_R_eq_B_R_B [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FibonacciParafermionFusionBridge.lean:40: theorem ofReal_B_matrix [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteCompassBraidedChain.lean:78: theorem permuteChain_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteCompassBraidedChain.lean:107: theorem braidTransport_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonBraiding.lean:57: theorem eps_fusion_eps [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonBraiding.lean:62: theorem one_mem_eps_fusion_eps [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonBraiding.lean:67: theorem eps_mem_eps_fusion_eps [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:57: theorem bitCharge_true [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:75: theorem computationalPath_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:86: theorem computationalPath_head [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:102: theorem nonComputationalCount_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:142: theorem oneQubitShape_true [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:164: theorem computationalBlockTriple_true [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:179: theorem singleQubitFullPath_true [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:223: theorem fourBlockEndpointPhase_epsilonPrime [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:238: theorem fourBlockBasisVector_ne [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:247: theorem singleQubitBasisVector_zero_eq_fourBlock [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:299: theorem setComputationalBit_ne [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:339: theorem computationalEndpointR_apply_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:348: theorem computationalEndpointR_apply_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:365: theorem twoQubitColexVector_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:370: theorem twoQubitColexVector_one_bits [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:382: theorem twoQubitColexVector_three [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:405: theorem twoQubit_tensorProduct_readback [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:437: theorem threeQubit_tensorProduct_readback [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:492: theorem fourBlockEndpointBraid_no_mixing [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:509: theorem fourBlockEndpointBraidAt_right [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:519: theorem fourBlockEndpoint_diagonal_summary [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:618: theorem fourBlockDualBasisVector_vacuum_coords [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:652: theorem liftFourBlockAction_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:785: theorem higherBlockDim_four [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:798: theorem higherBlockRecursiveSum_card [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:933: theorem recursiveDirectSumAction_inr [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:981: theorem lastGeneratorBlockAction_right [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:1112: theorem sectorGradeInvolution_right [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:1197: theorem braidDetExponent_three [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:1225: theorem updateComputationalBit_ne [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:1272: theorem evalComputationalWord_cons [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:1386: theorem evalSubgroupGenerator_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:1394: theorem evalSubgroupGenerator_ne [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:1430: theorem evalSubgroupWord_cons [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciAnyonRegister.lean:1440: theorem evalSubgroupWord_pair_comm_of_ne [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciCompassBridge.lean:35: theorem fibonacciCompassTransport_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciComputationalQubitPaperBridge.lean:34: theorem computational_vector_def [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciComputationalQubitPaperBridge.lean:39: theorem oneQubit_zero_label [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciComputationalQubitPaperBridge.lean:44: theorem oneQubit_one_label [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciComputationalQubitPaperBridge.lean:54: theorem computational_vector_card_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciComputationalQubitPaperBridge.lean:59: theorem computational_vector_card_two [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciComputationalSpace.lean:34: theorem card_computationalVector [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciComputationalSpace.lean:146: theorem blockDiagonalAction_preserves_noncomputational [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciComputationalSpace.lean:167: theorem localQubitAction_apply_ne [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciFourAnyonBlocks.lean:89: theorem rExponent_fib [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciFourAnyonBlocks.lean:115: theorem diagonalRAction_channel [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciFourAnyonBlocks.lean:120: theorem diagonalRAction_vacuum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciFourAnyonBlocks.lean:126: theorem diagonalRAction_fib [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciFourAnyonBlocks.lean:140: theorem fourAnyonGeneratorAction_first_eq_last [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciFourAnyonBlocks.lean:147: theorem fourAnyonGeneratorAction_first_channel [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciFourAnyonBlocks.lean:154: theorem fourAnyonGeneratorAction_last_channel [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciFourAnyonHestenesBridge.lean:49: theorem fourAnyonVacuumBasis_channel [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciFourAnyonHestenesBridge.lean:54: theorem fourAnyonFibBasis_channel [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciFourAnyonPaperBridge.lean:42: theorem fourAnyonChannel_vacuum_toBool [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciFourAnyonPaperBridge.lean:47: theorem fourAnyonChannel_fib_toBool [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciFourAnyonPaperBridge.lean:82: theorem fourAnyon_vacuumBasis_phase [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciFourAnyonPaperBridge.lean:88: theorem fourAnyon_fibBasis_phase [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciFourAnyonPaperBridge.lean:94: theorem fourAnyon_b1_diagonal [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciFourAnyonPaperBridge.lean:99: theorem fourAnyon_b3_diagonal [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciFourAnyonPaperBridge.lean:104: theorem fourAnyon_b1_eq_b3 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciFourPointBlocks.lean:50: theorem phi1_snd [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciFourPointBlocks.lean:72: theorem diagonalBraidAction_phi0 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciFourPointBlocks.lean:77: theorem diagonalBraidAction_phi1 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciFourPointBlocks.lean:94: theorem b1Action_phi0 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciFourPointBlocks.lean:99: theorem b1Action_phi1 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciFourPointBlocks.lean:104: theorem b3Action_phi0 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciFourPointBlocks.lean:109: theorem b3Action_phi1 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciFourPointBlocks.lean:117: theorem b1Action_eq_b3Action [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciFourPointDualBasis.lean:62: theorem fusionMatrix_apply_snd_snd [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciFourPointDualBasis.lean:109: theorem theta1_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciGeneralBnPaperBridge.lean:71: theorem general_blockDimension_step_from_recursive [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciGeneralBraidGenerators.lean:95: theorem twoBlockDiagonal_left_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciGeneralBraidGenerators.lean:102: theorem twoBlockDiagonal_right_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciGeneralBraidGenerators.lean:126: theorem threeBlockDiagonal_first_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciGeneralBraidGenerators.lean:133: theorem threeBlockDiagonal_middle_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciGeneralBraidGenerators.lean:215: theorem determinantExponent_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciGeneralBraidGenerators.lean:219: theorem determinantExponent_step [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciHigherAnyonPaperBridge.lean:95: theorem finiteLocalDoubletMatrix_independent_of_r [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciLowAnyonMatrices.lean:79: theorem pi5_endpoint_templates [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciLowAnyonMatrices.lean:85: theorem pi5_b2_lower_block [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciLowAnyonMatrices.lean:141: theorem pi6_b2_repeated_B_blocks [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciLowAnyonMatrices.lean:153: theorem pi6_b5_diagonal_entries [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciLowAnyonPaperBridge.lean:29: theorem sectionSix_basis5_card [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciLowAnyonPaperBridge.lean:34: theorem sectionSix_basis6_card [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciLowAnyonPaperBridge.lean:70: theorem sectionSix_n6_endpoint_templates [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciMonodromyInterface.lean:56: theorem braidWordAction_cons [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciMonodromyInterface.lean:99: theorem electronBlindBraidAction_independent_of_r [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciPailRopeQubits.lean:119: theorem withInertEndpoints_length [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciPailRopeQubits.lean:124: theorem withoutInertEndpoints_length [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciPailRopeQubits.lean:142: theorem oneQubitOne_bit [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciPaperBridge.lean:139: theorem fibonacci_fourPoint_phi0 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciPaperBridge.lean:144: theorem fibonacci_fourPoint_phi1 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciPaperBridge.lean:149: theorem fibonacci_fourPoint_b1_diagonal [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciPaperBridge.lean:154: theorem fibonacci_fourPoint_b3_diagonal [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciPaperBridge.lean:169: theorem fibonacci_fourPoint_theta0 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciPaperBridge.lean:174: theorem fibonacci_fourPoint_theta1 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciQubitNoLeakage.lean:134: theorem twoQubitNoLeakageAction_nc [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciQubitNoLeakageBridge.lean:27: theorem computational_vector_def [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciRegisterWords.lean:101: theorem registerWordComputationalAction_cons [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciRegisterWords.lean:119: theorem registerGeneratorComputationalAction_left_apply_first [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciRegisterWords.lean:126: theorem registerGeneratorComputationalAction_right_apply_last [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciRegisterWords.lean:133: theorem registerGeneratorComputationalAction_even_apply_same [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciRegisterWords.lean:139: theorem registerGeneratorComputationalAction_even_apply_ne [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciSparseLowAnyonMatrices.lean:63: theorem sparseBraidMatrix_nil_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciSparseLowAnyonMatrices.lean:69: theorem sparseBraidMatrix_single_B00 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciSparseLowAnyonMatrices.lean:75: theorem sparseBraidMatrix_single_B01 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciSparseLowAnyonMatrices.lean:88: theorem sparseBraidMatrix_single_B11 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciSparseLowAnyonMatrices.lean:165: theorem pi7_b2_first_block [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciSparseLowAnyonPaperBridge.lean:28: theorem sectionSix_basis7_card [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciSparseLowAnyonPaperBridge.lean:33: theorem sectionSix_basis8_card [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciSparseLowAnyonPaperBridge.lean:38: theorem sectionSix_pi7_b1_phase [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciSparseLowAnyonPaperBridge.lean:44: theorem sectionSix_pi7_b6_phase [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciSparseLowAnyonPaperBridge.lean:50: theorem sectionSix_pi8_b1_phase [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteFibonacciSparseLowAnyonPaperBridge.lean:56: theorem sectionSix_pi8_b7_phase [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteJaynesCenteredScoreBridge.lean:90: theorem centeredScore_eq_sub [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteMajoranaBraid.lean:127: theorem parity3_braid_word_left [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteMajoranaBraiding.lean:32: theorem majoranaSwap_apply_right [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiniteMajoranaBraiding.lean:74: theorem evalBraidWord_cons [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FiveGradedTwistorIncidence.lean:119: theorem incident_of_incidenceEquation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FractalInvariantOperatorLimit.lean:190: theorem squareZeroFlux_eq_squareZeroLog [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FreeEntropyDiffusionBridge.lean:92: theorem souriauBoundaryEntropy_eq_expectation_surprisal [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FreeEntropyDiffusionBridge.lean:119: theorem freeEntropyPotential_eq_log_partition [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FreeEntropyDiffusionBridge.lean:125: theorem souriauSurprisal_eq_neg_log_gibbsWeight [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FreeEntropyDiffusionBridge.lean:131: theorem souriauBoltzmannEntropy_eq_weighted_surprisal_sum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FreeEntropyDiffusionBridge.lean:153: theorem souriauFreeEntropyFunctional_eq_massieu_sub_bregman [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/FreeEntropyDiffusionBridge.lean:187: theorem souriauBoundaryFreeEntropy_eq_entropy_sub_bregman [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/GeneralizedOperatorChiral.lean:84: theorem chiralExp_scalar_formula [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/GeneralizedOperatorChiral.lean:89: theorem chiralExp_directional_formula [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/GeneralizedOperatorChiral.lean:268: theorem ellipticExp_scalar_formula [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/GeneralizedOperatorChiral.lean:272: theorem ellipticExp_directional_formula [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/GeneralizedOperatorChiral.lean:301: theorem parabolicExp_scalar_formula [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/GeneralizedOperatorChiral.lean:305: theorem parabolicExp_directional_formula [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/GeometricCalculusFreudenthalBridge.lean:328: theorem horizonOperator_eq_projector [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/GeometricCalculusSTUBridge.lean:64: theorem stuFreudenthalChargeGeometry_I4 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/GeometricCalculusSTUBridge.lean:91: theorem stuQubitChargeGeometry_I4 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/GeometricQuantization.lean:25: theorem m2_b_function_poly_root_neg_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/GeometricStokes.lean:67: theorem stokesBivectorResidue_eq_two_pi_smul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/GrandCanonicalExperts.lean:409: lemma diracAction_add_right [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/GrandCanonicalPrimeEnsembleFormulas.lean:154: theorem primeEffectiveEnergy_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/GrandCanonicalPrimeEnsembleFormulas.lean:165: theorem primeBoltzmannWeight_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/GrandCanonicalPrimeEnsembleProofs.lean:48: theorem energy_eq_log_volume [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/HadjiivanovMonodromyProjection.lean:58: theorem braid_hecke_relation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/HadjiivanovMonodromyProjection.lean:155: theorem virasoro_L0_trace [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/HartwigSouriauFrameDrazin.lean:105: theorem principalIdempotent_eq_drazin_complement [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/HasseWeilZetaPointCounts.lean:41: theorem LogZeta_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/HaugManiYinYangBridge.lean:92: theorem phaseAxis_eq_J_mul_eps [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/HaugManiYinYangBridge.lean:96: theorem phaseAxis_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/HaugManiYinYangBridge.lean:118: theorem realDoubledScalar_I [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/HaugManiYinYangBridge.lean:123: theorem realDoubledScalar_I_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Herm2x2OsO55RationalBridge.lean:143: theorem conj44Vec_preserves_q44 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Herm2x2OsO55RationalBridge.lean:170: theorem conjugateTransverse_preserves_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Herm2x2OsO55RationalBridge.lean:220: theorem nullSwap_preserves_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/HestenesKreinVacuum.lean:46: theorem a_eq_N [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/HestenesKreinVacuum.lean:53: theorem krein_adjoint_P [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/HilbertCuntz.lean:43: theorem K_op_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/HilbertCuntz.lean:49: theorem S_left_apply_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/HilbertCuntz.lean:51: theorem S_left_apply_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/HodgeKreinDeterminantBridge.lean:93: theorem det_one_add_nilpotent_2x2 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/HodgeKreinSuperLaplacian.lean:103: theorem P_nil_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/HodgeStar4D.lean:34: lemma gamma5_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/HodgeStarSelfDualAlgebra.lean:74: theorem P_minus_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/HolographicEntanglementSymmetry.lean:69: theorem sectorSubtreeEntropy_triality_invariant [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/HolographicEntanglementSymmetry.lean:73: theorem sectorMinimalSurfaceArea_triality_invariant [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/HolographicTensorFactorSeparation.lean:63: theorem geom_color_commutator_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/HypercomplexTriadVirasoroBridge.lean:64: theorem highestWeight_of_vacuum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/HypercomplexTriadVirasoroBridge.lean:112: theorem cocycle_on_opposite_modes [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/HypercomplexTriadVirasoroBridge.lean:140: theorem LminusOne_vacuum_of_N_vacuum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/InductiveOperatorTaylorClosure.lean:41: theorem operatorTaylorPrefix_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/IntegralZornII44Bridge.lean:62: theorem ii44Dual_involutive [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/InverseKernelAlgebra.lean:42: theorem spectralProjector_add_spectralComplementaryProjector [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/InverseKernelAlgebra.lean:47: theorem mpRangeProjector_add_mpRangeComplementaryProjector [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/InverseKernelAlgebra.lean:52: theorem metricProjector_add_metricComplementaryProjector [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/InverseKernelCartanCore.lean:71: theorem GammaS_eq_two_mul_spectralProjector_sub_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ItFromBit.lean:77: theorem word_readout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ItFromBit.lean:117: theorem basisEquiv_readout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ItFromBit.lean:270: theorem walk_readout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ItFromBit.lean:275: theorem drazinHodgeFilter_readout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ItFromBit.lean:280: theorem kmsWeylWeight_readout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ItFromBit.lean:331: theorem word_readout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ItFromBit.lean:336: theorem cantorCylinder_readout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ItFromBit.lean:341: theorem projection_readout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ItFromBit.lean:346: theorem fock_readout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ItFromBit.lean:351: theorem walk_readout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/JordanWignerCelikKocakBridge.lean:282: theorem majoranaC_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/KLinearRepresentation.lean:109: lemma neg_kConjugate_comp_K [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/KLinearRepresentation.lean:114: lemma neg_K_comp_kConjugate [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/KapranovZetaSeries.lean:57: theorem oneSeries_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/KapranovZetaSeries.lean:112: theorem linearFactor_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/KapranovZetaSeries.lean:148: theorem quadraticFactor_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/KashiwaraCuntzCohomology.lean:118: theorem lowering_raising_section [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/KashiwaraCuntzCohomology.lean:158: theorem raiseRight_mirror_lowerLeft [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/KashiwaraCuntzCohomology.lean:166: theorem raiseLeft_mirror_lowerRight [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/KashiwaraCuntzCohomology.lean:175: theorem mirror_crystalCoboundary [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/KleinBottleBoundaryAction.lean:101: theorem glideReflection_eq_deck_sheet [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/KleinBoundaryStates.lean:30: theorem boundary_plus_J_fixed [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/KleinBoundaryStates.lean:35: theorem boundary_minus_J_anti [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/KleinBoundaryStates.lean:40: theorem boundary_plus_S_fixed [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/KleinBoundaryStates.lean:45: theorem boundary_minus_S_anti [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/KleinMonodromyRepresentationSpace.lean:80: theorem finite_klein_relation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/KleinMonodromyRepresentationSpace.lean:84: theorem finite_projective_sign [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/KreinCarrierInstances/Bridge.lean:28: theorem concreteBridgeKlein_kreinTrace [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/KreinCarrierInstances/CoreProjector.lean:44: theorem concreteCoreProjectorKlein_core_krein_selfadjoint [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/KreinCarrierInstances/Datum.lean:58: theorem modularGeneratorKlein_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/KreinCarrierInstances/RelativeFredholm.lean:31: theorem concreteRelativeFredholmKlein_relativePartitionReadout_eq_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/KreinCarrierInstances/RotorFlow.lean:15: theorem concreteRotorFlowKlein_rotor_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/KreinCarrierInstances/RotorFlow.lean:18: theorem concreteRotorFlowKlein_rotorInv_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/KreinProjectorLattice.lean:161: theorem sdiff_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/KreinProjectorLattice.lean:304: theorem kreinInvolution_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/LevelSeparationNoIso.lean:46: theorem finiteTomitaKreinAtom_finrank [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/LieOrbitAdjointInvariants.lean:42: theorem trace_adjointAction [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/LieOrbitAdjointInvariants.lean:46: theorem det_adjointAction [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/MatrixDetExpTraceJacobi.lean:70: theorem isUnit_matrixExpFlow [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/MatrixDetExpTraceJacobi.lean:75: theorem matrixExpFlow_neg_eq_inv [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/MatrixDetExpTraceJacobi.lean:118: theorem trace_matrixExpFlow_inv_mul_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/MatrixExponentialTraceDet.lean:367: lemma hasDerivAt_matrix_exp_smul_right [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/MatrixExponentialTraceDet.lean:376: lemma hasDerivAt_matrix_exp_smul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/MatrixExponentialTraceDet.lean:400: lemma trace_inv_mul_mul_of_isUnit [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/MatrixValuedDerivativeMoorePenrose.lean:34: theorem generalizedDifferenceQuotient_const [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/MaximumCaliberKLSplit.lean:55: theorem jeffreysDivergence_eq_symmetricDivergence [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/MaximumCaliberKLSplit.lean:60: theorem jeffreysDivergence_eq_half_sum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/MaximumCaliberPath.lean:80: theorem cycle_pathEntropyProduction_eq_cycleCurvatureLog [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/MetriplecticCore.lean:88: theorem leibniz_entropy_H_decompose [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ModularFluxVacuumFunctional.lean:124: theorem modularFluxVacuumFunctionalM2_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ModularInfinitesimalDictionary.lean:122: theorem arakiGradient_eq_barrierForce [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ModularLorentzBoost.lean:23: theorem K_eval [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ModularNilpotentFinite.lean:91: theorem modularFluxVacuumFunctional_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ModularSL2R.lean:39: theorem comm_N_N_transpose [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/MoebiusHurwitzDuality.lean:60: theorem fine_structure_mersenne_decomposition [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/MoebiusHurwitzDuality.lean:69: theorem m2_equals_su3_fundamental_dim [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/MoebiusHurwitzDuality.lean:78: theorem m3_equals_octonion_imaginary_dim [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/MongeAmpereCramerRao.lean:64: theorem absDet_cramerRaoMetric_eq_one_of_incompressible [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/NavierStokesSnapBridge.lean:340: theorem projected_extreme_has_gradeTwo_memory [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/NoncommutativeOperatorAlgebra.lean:111: theorem typeIII_baseIntegral_eq_modularWeight_integral [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/O55LightConeSpectrumBridge.lean:89: theorem intercept_zero_reduces_standard_massSq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/O55LightConeSpectrumBridge.lean:96: theorem doubled_ground_massSq_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/O55LightConeSpectrumBridge.lean:101: theorem doubled_first_excited_massSq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/OperatorJKOStep.lean:119: theorem objective_le_previous_energy [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/OperatorSurgery.lean:246: theorem identitySplit_projector_nil [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/OperatorThermodynamics.lean:226: theorem partitionPotential_eq_freeEnergy [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PerelmanWCore.lean:33: lemma deriv_WFunctional_eq_of_law [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Pfaffian.lean:17: theorem det_skew_2x2 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Pfaffian.lean:22: theorem pfaffian_sq_eq_det_2x2 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Pfaffian.lean:27: theorem pfaffian_zero_2x2 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PhotonicParabolicTransfer.lean:30: theorem det_T [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PhysicsOfInformationCore.lean:115: theorem bridge_totalMass_preserved [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PhysicsOfInformationCore.lean:123: theorem bridge_modeEntropy_preserved [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PhysicsOfInformationCore.lean:131: theorem bridge_parityEntropy_preserved [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PhysicsOfInformationCore.lean:138: theorem bridge_semanticState_eq_canonical [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PiCylinderMathlib.lean:52: theorem pure_mem_canonicalCylinder_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PiCylinderMathlib.lean:58: theorem pure_mem_finsetCanonicalCylinder_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Pin55CliffordBridge.lean:45: theorem two_smul_D5 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Pin55CliffordBridge.lean:49: theorem two_smul_D4 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PrimeBooleanCubeSugawara.lean:95: theorem trivialVirasoroDatum_central [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PrimeCocycleCoefficients.lean:48: theorem cocycleCoefficient_empty [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PrimeCocycleCoefficients.lean:55: theorem cocycleCoefficient_singleton [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PrimeFibonacciLattice.lean:21: theorem ratio_converges_to_phi [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PrimeFibonacciLattice.lean:26: theorem most_irrational_barrier [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PrimeLeeYangFerromagneticChain.lean:142: theorem couplingMatrix_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PrimeLeeYangFerromagneticChain.lean:245: theorem occupation_down [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PrimeLeeYangHopfieldLimitBridge.lean:48: theorem hopfieldFullCoupling_eq_centeredSpinCoupling [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PrimeLeeYangHopfieldLimitBridge.lean:53: theorem hopfieldFullCoupling_eq_outerProduct [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PrimeParafermionGrandCanonicalClock.lean:62: theorem stateProbability_eq_kappa_normalized_weight [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PrimeParafermionGrandCanonicalClock.lean:87: theorem ln_Q_is_massieu [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PrimeParafermionGrandCanonicalClock.lean:92: theorem parafermionGrandPotential_eq_neg_inv_beta_mul_log_Q [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PrimeParafermionGrandCanonicalClock.lean:98: theorem parafermionLocalFactor_eq_geomSum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PrimeParafermionGrandCanonicalClock.lean:103: theorem parafermionLocalFactor_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PrimeParafermionGrandCanonicalClock.lean:117: theorem parafermionLocalFactor_two [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PrimeParafermionGrandCanonicalClock.lean:122: theorem stateProbability_two [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PrimeParafermionGrandCanonicalClock.lean:127: theorem parafermionLocalFactor_three [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PrimeParafermionGrandCanonicalClock.lean:132: theorem stateProbability_three [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PrimeParafermionGrandCanonicalClock.lean:241: theorem partition_eq_prod [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PrimeParafermionGrandCanonicalClock.lean:246: theorem massieu_eq_log_partition [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PrimeParafermionGrandCanonicalClock.lean:251: theorem grandPotential_eq_neg_inv_beta_mul_massieu [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PrimeParafermionGrandCanonicalClock.lean:257: theorem boltzmannEntropy_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PrimeParafermionGrandCanonicalClock.lean:328: theorem z3_localFactor_eq_trinomial [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PrimeSUSYVacuum.lean:57: theorem finiteWittenIndexSum_eq_powerset_sum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/PrimeVirasoroSugawara.lean:581: theorem heisenberg_sugawara_centralCharge_eq_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ProjectedLFunctionCalibration.lean:21: theorem cuspidalLFunction_eq_raw_of_siegel_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ProjectedLFunctionCalibration.lean:33: theorem projectedL_eval_eq_projected [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ProjectedLFunctionCalibration.lean:45: theorem projectedL_resonance_iff_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ProjectiveCCR.lean:46: theorem excitedStateSector_eq_orthogonal [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ProjectiveFoundation.lean:752: theorem baseAction_is_genuine [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ProofCausalityBridge.lean:29: theorem forwardCone_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ProofCausalityBridge.lean:34: theorem backwardCone_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/QuantumGeometryDualSheetBridge.lean:24: theorem cramerRaoMetricOp_eq_quantumGeometryOp [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/QuaternionCondensate.lean:121: theorem normSq_conj [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/QuaternionCondensate.lean:143: theorem normSq_phase [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/RecursiveClosureBridge.lean:59: theorem state_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/RelativeModularCenteredFunctional.lean:577: theorem cantorMellinKernel_eq_one_iff_phaseAxis [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/RindlerWeylDecomposition.lean:89: theorem log_r_eq_xi_add_eta [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/RindlerWeylDecomposition.lean:94: theorem log_s_eq_xi_sub_eta [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/RoseDrazinComputation.lean:53: theorem ell_readout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/RoseDrazinComputation.lean:57: theorem p_readout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/RoseDrazinComputation.lean:61: theorem characteristicPolynomial_readout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/RoseDrazinComputation.lean:66: theorem nonzeroCharacteristicPart_readout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/RoseDrazinComputation.lean:71: theorem degreeBound_readout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/RoseDrazinComputation.lean:75: theorem rosePolynomial_readout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/RoseDrazinComputation.lean:118: theorem B_readout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/RoseDrazinComputation.lean:122: theorem p_readout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/RoseDrazinComputation.lean:126: theorem rIndex_readout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/RoseDrazinComputation.lean:130: theorem sIndex_readout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/RoseDrazinComputation.lean:134: theorem annihilatingPolynomial_readout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/RoseDrazinComputation.lean:139: theorem drazinIndex_readout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/RoseDrazinComputation.lean:227: theorem exponent_readout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/RyuTakayanagiEntanglementBridge.lean:114: theorem minimalSurfaceArea_is_proportional_to_depth [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SL2FiveGradingExample.lean:41: lemma e_mem_sl [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SL2FiveGradingExample.lean:42: lemma f_mem_sl [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SO3FenchelDuality.lean:57: theorem casimir_invariant_on_orbit [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SO3FenchelDuality.lean:93: theorem kinetic_invariant [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SO3FenchelDuality.lean:97: theorem dual_invariant [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SO3FenchelDuality.lean:120: theorem dualBregman_zero_diag [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SO3FenchelDuality.lean:385: theorem so3_coadjointPairing_eq_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SO3FenchelDuality.lean:390: theorem so3_kksForm_eq_lieKks [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SUSYRecursiveSchema.lean:33: theorem adPow_H_Q_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Sandbox/NativeQuaternionPauli.lean:75: theorem comm_qI_qJ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Sandbox/NativeQuaternionPauli.lean:78: theorem comm_qJ_qK [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Sandbox/NativeQuaternionPauli.lean:81: theorem comm_qK_qI [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Sandbox/NativeQuaternionPauli.lean:84: theorem anticomm_qI_qI [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Sandbox/NativeQuaternionPauli.lean:87: theorem anticomm_qJ_qJ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Sandbox/NativeQuaternionPauli.lean:90: theorem anticomm_qK_qK [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Sandbox/NativeQuaternionPauli.lean:93: theorem anticomm_qI_qJ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Sandbox/NativeQuaternionPauli.lean:96: theorem anticomm_qJ_qK [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Sandbox/NativeQuaternionPauli.lean:141: theorem comm_sI_sJ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Sandbox/NativeQuaternionPauli.lean:144: theorem comm_sJ_sK [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Sandbox/NativeQuaternionPauli.lean:147: theorem comm_sK_sI [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Sandbox/NativeQuaternionPauli.lean:150: theorem anticomm_sI_sI [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Sandbox/NativeQuaternionPauli.lean:153: theorem anticomm_sJ_sJ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Sandbox/NativeQuaternionPauli.lean:156: theorem anticomm_sK_sI [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Sandbox/NativeQuaternionPauli.lean:159: theorem anticomm_sK_sK [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Sandbox/NativeQuaternionPauli.lean:162: theorem anticomm_sI_sJ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/Sandbox/NativeQuaternionPauli.lean:165: theorem anticomm_sJ_sK [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SectorLattice.lean:63: theorem elementarySector_inf_eq_meet [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SelfDualNormalConeBridge.lean:41: theorem primitiveToPrimeProjectiveKL_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SelfDualNormalConeBridge.lean:51: theorem primeToPrimitiveProjectiveKL_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SingularBoundaryCorrection.lean:124: theorem boundaryGenerator_eq_projector_commutator [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SingularBoundaryCorrection.lean:130: theorem rightBoundaryGenerator_eq_projector_commutator [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SingularityCausalCoupling.lean:43: theorem milnor_monodromy_coupling [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SouriauCasimirInvariantSL2Model.lean:30: theorem coAd0_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SouriauCasimirInvariantSL2Model.lean:32: theorem coAd0_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SouriauCasimirInvariantSL2Model.lean:36: theorem theta0_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SouriauCasimirInvariantSL2Model.lean:38: theorem theta0_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SouriauCasimirInvariantSL2Model.lean:43: theorem sl2_affine_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SouriauCasimirInvariantSL2Model.lean:48: theorem sl2_affine_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SouriauCasimirInvariantSL2Model.lean:65: theorem sl2_entropy_affine_invariant [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SouriauCasimirInvariantSL2Model.lean:74: theorem sl2_operatorFenchel_contact_affine_preserved [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SouriauCasimirInvariantSL2Model.lean:91: theorem sl2_operatorFenchelGap_invariant [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SouriauDensityWeightContext.lean:61: theorem densityWeight_eq_numberWeight [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SouriauDiracHodgeCoupling.lean:89: theorem projector_swap_by_definition [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SouriauDiracHodgeCoupling.lean:178: theorem krein_operator_hodge_dual_definition [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SouriauDiracHodgeCoupling.lean:249: theorem representedS_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SouriauDiracHodgeCoupling.lean:411: theorem operator_hodge_dual_definition [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SouriauDiracHodgeCoupling.lean:487: theorem representedS_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SpecialLinearLieAlgebra.lean:33: theorem my_trace_eq_matrix_trace [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SpecialLinearLieAlgebra.lean:38: lemma my_trace_add [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SpecialLinearLieAlgebra.lean:43: lemma my_trace_sub [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SpecialLinearLieAlgebra.lean:48: lemma my_trace_smul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SpecialLinearLieAlgebra.lean:53: lemma my_trace_mul_comm [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SpectralGeneratorProxy.lean:50: theorem axis [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SpectralGeneratorProxy.lean:89: theorem sub [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SpectralGeneratorProxy.lean:215: theorem denominator_right_inverse [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SpectralInference.lean:142: theorem spectralProjector_idempotent [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SpinorGradeParityEscape.lean:55: theorem temporalVielbein_closed_form [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitAlbert.lean:188: theorem splitAlbertCarrier_finrank_eq_27 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCARCurrentSource.lean:211: theorem chargedFockSpace_current_commutator_one_negOne [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCARCurrentSource.lean:226: theorem chargedFockSpace_current_commutator_zero_of_add_ne_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCayleyDicksonTrace.lean:41: theorem splitSquareTraceSign_of_even [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCayleyDicksonTrace.lean:46: theorem splitSquareTraceSign_of_odd [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCayleyDicksonTrace.lean:59: theorem splitBladeCount_eq_two_pow_add [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCayleyDicksonTrace.lean:64: theorem splitPureBladeCount_eq_two_pow_add_sub_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordCantorFock.lean:194: theorem cantorState_hop_false_eq_create [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordCantorHop.lean:133: theorem cantorState_hop_false_eq_create [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordCantorHop.lean:138: theorem cantorState_hop_true_eq_annihilate [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordCurrentLift.lean:45: theorem splitCliffordInfinityCurrentDatum_killingForm [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordCurrentLift.lean:51: theorem splitCliffordInfinity_current_mode_bracket [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordFiniteCAR.lean:65: theorem JfinIndexed_eq_zero_of_ne_one_ne_neg_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordFiniteCAR.lean:98: theorem JfinIndexed_eval_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordFiniteCAR.lean:103: theorem JfinIndexed_eval_neg_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordFiniteCAR.lean:108: theorem Jmode_comm_01_01 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordFiniteCAR.lean:113: theorem Jmode_comm_10_10 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordFiniteCAR.lean:659: theorem completedCurrentModeJW_comm_table_piecewise [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordFiniteCAR.lean:824: theorem completedCurrentModeJW_pairComm_finsum_eq_zero_of_add_eq_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordFiniteCAR.lean:833: theorem completedCurrentModeJW_pairComm_finsum_eq_zero_of_add_ne_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordHeisenbergBridge.lean:90: theorem toCurrentHeisenbergRep_trunc [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordHeisenbergBridge.lean:125: theorem toCurrentSugawaraMorphism_virasoro [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordInfiniteCurrent.lean:55: theorem lie_Jinf_one_neg_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordJordanWignerTwoMode.lean:33: theorem car_mode1 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordJordanWignerTwoMode.lean:36: theorem car_mode2 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordJordanWignerTwoMode.lean:39: theorem car_cross_annihilate [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordJordanWignerTwoMode.lean:42: theorem car_cross_annihilate_create [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordJordanWignerTwoMode.lean:45: theorem Jfin_eq_zero_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordJordanWignerTwoMode.lean:48: theorem Jfin_trunc_vector [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordJordanWignerTwoMode.lean:57: theorem Jfin_comm_1_1 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordJordanWignerTwoMode.lean:60: theorem Jfin_comm_neg1_neg1 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordJordanWignerTwoModeCurrent.lean:86: theorem Jfin_eval_neg_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordJordanWignerTwoModeCurrent.lean:108: theorem Jfin_eq_zero_of_ne_one_ne_neg_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordJordanWignerTwoModeCurrent.lean:156: theorem Jfin_comm_1_1 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordJordanWignerTwoModeCurrent.lean:161: theorem Jfin_comm_neg1_neg1 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordO55TKKClosure.lean:35: lemma so55_dim [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordSourceCurrent.lean:160: theorem cutoffCurrentMode_insert [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordSourceCurrentWick.lean:50: theorem commutator_eq_zero_of_add_ne_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordSourceCurrentWick.lean:62: theorem commutator_eq_central_of_add_eq_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordSourceCurrentWick.lean:97: theorem normalOrderedCurrent_commutator_limit_exchange [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordSourceCurrentWick.lean:185: theorem representedChargedFockJ_heisenberg_comm_full [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordSourceCurrentWick.lean:611: theorem sourceJfin_mode_two_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordSourceCurrentWick.lean:618: theorem sourceJfin_mode_neg_two_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordSourceCurrentWick.lean:782: theorem sourceJfin_pairComm_finsum_eq_zero_of_add_ne_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordSourceCurrentWick.lean:794: theorem sourceJfin_pairComm_finsum_eq_zero_of_add_eq_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordSourceCurrentWick.lean:939: theorem rawCAR_heisenberg_comm_zero_offdiag [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordSourceCurrentWick.lean:953: theorem rawCAR_heisenberg_comm_central_diag [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordSourceCurrentWick.lean:1199: theorem externalInfiniteJ_splitSourceEndWickLaw [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordSourceCurrentWick.lean:1672: theorem jw_mode_trunc_vector_infinite [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordSourceCurrentWick.lean:1760: theorem heisenberg_comm_one_neg_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordSourceCurrentWick.lean:1771: theorem heisenberg_comm_one_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordSourceCurrentWick.lean:2299: theorem virasoro_jacobi [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordSourceSuperVirasoroFiniteWindow.lean:291: theorem G_trunc_eq_zero_of_psi_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordSourceWickBaseExternalBridge.lean:25: theorem local_wick_mode_one_seed [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordSuperVirasoroModes.lean:54: theorem shifted_supercurrent_self_anticomm_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordTwoModeCAR.lean:98: theorem traceForm4_cross_annihilate_anticommute [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordTwoModeCAR.lean:103: theorem traceForm4_cross_mixed_anticommute [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitCliffordTwoModeCAR.lean:108: theorem traceForm4_mode1_car [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitHierarchy.lean:153: theorem canonicalDiagnostic_localSeed [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitHierarchy.lean:158: theorem canonicalDiagnostic_quaternionTier [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitHierarchy.lean:163: theorem canonicalDiagnostic_octonionTier [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitHierarchy.lean:168: theorem canonicalDiagnostic_trialityPlacement [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitHierarchy.lean:173: theorem canonicalDiagnostic_localSeed_signature [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitHierarchy.lean:178: theorem canonicalDiagnostic_quaternionTier_signature [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitOctonionAssociator.lean:49: theorem associatorDefect_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitOctonionAssociator.lean:61: theorem associatorDefect_zero_of_associative [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitOctonionAssociator.lean:80: theorem cocycleAssociatorDefect_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitQuaternionConcrete.lean:56: theorem zero_def [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitQuaternionConcrete.lean:167: theorem det_2x2_eq_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitQuaternionMatrixModel.lean:122: theorem splitComplexMatrix_det_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitQuaternionMatrixModel.lean:127: theorem splitComplexMatrix_det_neg_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitQuaternionMatrixModel.lean:230: theorem splitNilpotents_explicit [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitQuaternionMatrixModel.lean:235: theorem splitNilpotentPlus_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SplitQuaternionMatrixModel.lean:239: theorem splitNilpotentMinus_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/StableVacuum.lean:212: theorem finiteExcitationVolumeExpectation_eq_zero_of_vacuum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/StableVacuum.lean:261: theorem finiteExcitationVolume_apply_vacuum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/StandardQuaternionIsomorphism.lean:35: theorem e23_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/StandardQuaternionIsomorphism.lean:36: theorem e31_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/StandardQuaternionIsomorphism.lean:37: theorem e12_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/StandardQuaternionIsomorphism.lean:39: theorem cross_12_23 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/StandardQuaternionIsomorphism.lean:40: theorem cross_23_31 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/StoneCantorMathlib.lean:39: theorem principalUltrafilter_prefixCylinder_eval [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SuperBracketHestenesKreinClosure.lean:47: theorem apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SuperBracketHestenesKreinClosure.lean:64: theorem neg [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SuperBracketHestenesKreinClosure.lean:69: theorem sub [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SuperBracketHestenesKreinClosure.lean:90: theorem even_commutator_even [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SuperBracketHestenesKreinClosure.lean:96: theorem even_odd_commutator_odd [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SuperBracketInvolutionParity.lean:248: theorem superBracket_odd_odd_self_eq_square_add_square [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SupergradedMetriplecticCore.lean:52: theorem leibniz_entropy_H_decompose [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/SymmetryClosureConformalBlocks.lean:103: theorem preservesSectors_sub [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/TKKJordanPairData.lean:59: theorem gradeAdd_p2_p1_none [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/TKKJordanPairData.lean:61: theorem gradeAdd_m2_m1_none [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/TKKJordanPairData.lean:64: theorem gradeAdd_m1_p1 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/TensorModularAtomCurrent.lean:40: theorem wickContraction_current [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ThermodynamicChiralGraphCalculus.lean:617: theorem entropyProduction_nonneg_of_pointwise [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ThermodynamicChiralGraphCalculus.lean:844: theorem detailedBalance_iff_graph_cycle_ratio_product_eq_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/TimeAsWindingMonodromy3D.lean:69: theorem boundary_eq_det_zero_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/TimeAsWindingMonodromy3D.lean:83: theorem Splus_det_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/TimeAsWindingMonodromy3D.lean:86: theorem Sminus_det_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/TomitaDissipativeBreak.lean:212: theorem channelOfNilpotent_omega_eq_parabolic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/TomitaDissipativeBreak.lean:219: theorem chiral_collapse_to_parabolic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/TomitaDissipativeBreak.lean:369: theorem dissipative_potential_le_initial [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/TopologicalEuler.lean:23: theorem euler_is_invariant [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/TorsionSpinorEinsteinFinite.lean:66: theorem contorsion_eq_half_cyclic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/TorsionStructure.lean:64: theorem vectorTorsion_zero_of_lower_symmetric [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/TorsionStructure.lean:109: theorem coordinate_cartanTorsionCoeff_eq_vectorTorsion [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/TorsionStructure.lean:124: theorem contorsionCoeff_zero_of_torsion_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/TorsionStructure.lean:174: theorem quaternionTorsion_zero_of_commuting [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/TransportLieDerivative.lean:177: lemma hasDerivAt_expTransportEnd_at_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/TransportLieDerivative.lean:183: theorem deriv_expTransportEnd_at_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/TransportLieDerivative.lean:417: theorem deriv_hestenesTransport_at_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/TriFacetLinearMap.lean:31: lemma P_hyp_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/TriFacetLinearMap.lean:32: lemma P_ell_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/TriFacetLinearMap.lean:33: lemma P_par_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/TrialitySpin8Permutations.lean:77: theorem trialitySectorTransport_vector_to_spinorPlus [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/TrialitySpin8Permutations.lean:81: theorem trialitySectorTransport_spinorPlus_to_spinorMinus [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/TrialitySpin8Permutations.lean:85: theorem trialitySectorTransport_spinorMinus_to_vector [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/TrichotomySummaryTheorems.lean:15: theorem row_elliptic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/TrichotomySummaryTheorems.lean:20: theorem row_hyperbolic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/TrichotomySummaryTheorems.lean:25: theorem row_parabolic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/TrichotomySummaryTheorems.lean:30: theorem row_projective [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/TwoSheetComplexPolarization.lean:160: theorem diracHodgeHopping_eq_shift_sum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/TypeIIIModularCantorSystem.lean:157: theorem antiDiagonal_antiSelfDual [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/UHFBooleanProjectionCantorBridge.lean:67: theorem cylinder_atom_boundaryPrefix_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/UHFBooleanProjectionCantorBridge.lean:205: theorem pointStoneFilter_prefixPullback [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/UHFBooleanProjectionCantorBridge.lean:265: theorem cantorBooleanEvaluation_eq_true_iff_pointStoneFilter [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/UHFBooleanProjectionCantorBridge.lean:458: theorem pointStoneUltrafilter_mem_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/UHFBooleanProjectionCantorBridge.lean:464: theorem finiteStoneSpectrum_prefixPullback [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/UHFBooleanProjectionCantorBridge.lean:581: theorem stoneBooleanEvaluation_eq_true_iff_selected [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/UHFInductiveColimitBoundary.lean:53: theorem diagEmbedSucc_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/UHFInductiveColimitBoundary.lean:101: theorem cylinder_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/UnifiedMatrixQuantumGeometryFinite.lean:109: theorem trace_sigma1 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/UnifiedMatrixQuantumGeometryFinite.lean:113: theorem trace_sigma2 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/UnifiedMatrixQuantumGeometryFinite.lean:117: theorem trace_sigma3 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/UnifiedSuperchargeAlgebra.lean:2752: theorem projected_supercharge_eq_sub_chiral [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/UnifiedSuperchargeAlgebra.lean:2757: theorem projected_left_eq_commutator_PD_PL [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/UnifiedSuperchargeAlgebra.lean:2763: theorem projected_right_eq_commutator_PD_PR [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/UnifiedSuperchargeAlgebra.lean:3463: theorem hasDrazinIndexOneSurrogate_iff_parabolic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/V4Q8ProjectiveBridge.lean:197: theorem q8ToV4_m1 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/V4SemidirectS3Bridge.lean:171: theorem trialityAction_inv_smul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/V4SemidirectS3Bridge.lean:280: theorem cycle_conjugation_J [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/V4SemidirectS3Bridge.lean:284: theorem cycle_conjugation_S [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/V4SemidirectS3Bridge.lean:288: theorem cycle_conjugation_JS [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/VirasoroCasimirCentralChargeReadback.lean:38: theorem cocycle_on_opposite_modes [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/VirasoroCasimirCentralChargeReadback.lean:120: theorem cocycle_on_opposite_modes [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/VirasoroRecursiveSchema.lean:36: theorem adPowL_one_lgen [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/VirasoroRecursiveSchema.lean:43: theorem adPowL_one_lgen_of_ne_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/VirasoroRecursiveSchema.lean:48: theorem adPowL_one_lgen_of_add_eq_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/VirasoroWardEquilibrium.lean:94: theorem wardConstraint_iff_wardResidual_eq_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/VolumeDeformationPrinciple.lean:91: theorem character_mulCommutator_eq_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/WeylMobiusReflection.lean:34: theorem weyl_involution [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/WilsonSchwingerBridge.lean:31: theorem schwingerWilsonLoop_defect [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/WittenMoebiusChiralParityIndex.lean:104: theorem chiralPole_sum_eq_splitOne [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/YangMillsContinuum.lean:190: theorem modularAutomorphismGroup_eq_of_time_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ZeroTemperatureCrystallization.lean:47: theorem j_conjugation_flips_chiral_phase [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ZetaJuliaYangBaxterBridge.lean:33: theorem julia_lyapunov_is_golden_ratio [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ZornCliffordRepresentation.lean:14: lemma smul_a [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ZornCliffordRepresentation.lean:15: lemma smul_b [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ZornCliffordRepresentation.lean:16: lemma smul_x [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ZornCliffordRepresentation.lean:17: lemma smul_y [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ZornCliffordRepresentation.lean:19: lemma add_a [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ZornCliffordRepresentation.lean:20: lemma add_b [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ZornCliffordRepresentation.lean:21: lemma add_x [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ZornCliffordRepresentation.lean:22: lemma add_y [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ZornCliffordRepresentation.lean:24: lemma sub_a [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ZornCliffordRepresentation.lean:25: lemma sub_b [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ZornCliffordRepresentation.lean:26: lemma sub_x [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ZornComposition.lean:26: theorem detZ_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ZornIntegralSpinSubgroup.lean:56: theorem zornBaseChange_y [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ZornLegitimateFacts.lean:34: theorem zornCoord_finrank_eq_8 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ZornLegitimateFacts.lean:38: theorem upperVectorZorn_isNull [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ZornLegitimateFacts.lean:43: theorem lowerVectorZorn_isNull [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ZornOuterTrialityGroup.lean:29: theorem zornTrace_triality [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ZornTrialityTKKBridge.lean:102: theorem laneGrade_mirror_associator [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ZornVectorMatrixExplicit.lean:168: theorem zornOne_eq_scalarZorn_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Canonical/ZornVectorMatrixExplicit.lean:256: theorem isZornNull_iff_norm_eq_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Cantor/CantorRandomWalk.lean:105: theorem localQuantumFlipStep_eq_componentN [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Cantor/CantorRandomWalk.lean:113: theorem cantor_noise_accumulation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Capstone/BenamouBrenierBridge.lean:78: lemma jkoFunctor_map_homOfLE_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Capstone/ErlangenLanglandsConcrete.lean:90: theorem langlands_lfunction_identity_is_recorded_as_debt [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Capstone/ErlangenLanglandsUnification.lean:71: theorem langlands_lfunction_zeta_is_recorded_as_obligation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Cartan/Involution.lean:113: lemma Pplus_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Cartan/Involution.lean:116: lemma Pminus_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Categorical/CFTBlocks.lean:4: theorem cross_ratio_translation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Categorical/CFTBlocks.lean:6: theorem cross_ratio_scale [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Categorical/CFTPrimary.lean:7: theorem descendant_norm [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Categorical/CuntzToFibonacciBoundaryFunctor.lean:67: theorem functor_obj_true [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Categorical/FibonacciBraidedTowerCone.lean:36: theorem fibonacci_yang_baxter_iso [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Categorical/FibonacciBraidedTowerCone.lean:46: theorem fibonacci_hexagon_forward_iso [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Categorical/FibonacciBraiding.lean:20: theorem F_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Categorical/FibonacciBraiding.lean:25: theorem det_F [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Categorical/FibonacciFusionCategoryData.lean:68: theorem unit_mem_tau_tensor_tau [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Categorical/FibonacciTimeModularClock.lean:65: theorem tickMatrixIter_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Categorical/InductivePosetColimit.lean:70: theorem poset_hom_of_le_eq_homOfLE [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Categorical/ModularDoubledRealHopfFibration.lean:66: theorem sameFiber_refl [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Categorical/ZornUHFColimit.lean:261: theorem colimitProduct_add_left [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Categorical/ZornUHFColimit.lean:265: theorem colimitProduct_add_right [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Causal/CausalAlgebra.lean:207: theorem forwardCone_nonempty [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Causal/CausalAlgebra.lean:210: theorem backwardCone_nonempty [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Causal/CausalAlgebra.lean:217: theorem acyclicity [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Causal/CausalSpectralTriple.lean:77: theorem D_odd [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Causal/CausalSpectralTriple.lean:81: theorem J_D_commute [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Causal/CausalSpectralTriple.lean:100: theorem order_one_holds [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Causal/ProofGraphExteriorCalculus.lean:66: theorem grad_apply_of_edge [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Causal/ProofGraphExteriorCalculus.lean:72: theorem grad_apply_of_not_edge [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Causal/TriFacetInstantiation.lean:58: lemma B_add_left [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Causal/TriFacetInstantiation.lean:65: lemma B_comm [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Causal/ZornPresheaf.lean:26: theorem ZornVec3.map_dot [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Causal/ZornPresheafColimitBridge.lean:25: theorem diag_succ_preserves_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/AlbertBottConformalBridge.lean:57: theorem cl11_tensor_step_eq_owner [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/AlbertBottConformalBridge.lean:112: theorem cl44_complexification_equiv_eq_owner [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/BottFromCl44.lean:37: theorem cl55_from_cl44_splitBottStep_eq_owner [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/BudinichCliqueSpinor.lean:45: theorem graphCliqueGram_adj_eq_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/BudinichCliqueSpinor.lean:50: theorem graphCliqueGram_eq_one_of_not_adj [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/BudinichCliqueSpinor.lean:99: theorem isFinsetGramClique_iff_isGramClique [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/BudinichCliqueSpinor.lean:283: theorem budinichGraphVector_null [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/BudinichCliqueSpinor.lean:289: theorem budinichGraphVector_pairing [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/BudinichSpinorsNullVectors.lean:250: theorem spinor2_finrank [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Cl11CoordinateAlgebra.lean:268: theorem cl11_commutator_is_derivation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Cl11MarkovJonesEngine.lean:84: theorem cl11MarkovTraceNet_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Cl11Matrix.lean:109: lemma finrank_mat2 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Cl11TensorTower.lean:97: theorem wittCreationBase_eq_half_gamma_plus_phaseAxis [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Cl11TensorTower.lean:102: theorem wittAnnihilationBase_eq_half_gamma_sub_phaseAxis [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Cl11TensorTower.lean:218: theorem jwRealEncodedCreation_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Cl3ComplexMatrixProduct.lean:420: lemma finrank_prodMat2C [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Cl44GenerationRotation.lean:88: theorem canonicalGenerationRotationPacket_hierarchy [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Cl44Witt.lean:125: theorem witt_CAR_ne [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Cl44Witt.lean:151: theorem cl11_a_sq_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Cl44Witt.lean:155: theorem cl11_adag_sq_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Cl4ComplexMatrixPeriodicity.lean:210: theorem mat4C_complex_finrank [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Cl55SpinorChirality.lean:111: theorem gammaBasis55_eq_recursiveGammaTensor [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Cl55SpinorChirality.lean:117: theorem vec55SplitEquiv_basis0 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Cl55SpinorChirality.lean:121: theorem vec55SplitEquiv_basis5 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Cl55SpinorChirality.lean:125: theorem vec55SplitEquiv_basis1 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Cl55SpinorChirality.lean:130: theorem vec55SplitEquiv_basis6 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Cl55SpinorChirality.lean:169: theorem vec55SplitEquiv_basis2 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Cl55SpinorChirality.lean:174: theorem vec55SplitEquiv_basis7 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Cl55SpinorChirality.lean:179: theorem vec55SplitEquiv_basis3 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Cl55SpinorChirality.lean:184: theorem vec55SplitEquiv_basis8 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Cl55SpinorChirality.lean:189: theorem vec55SplitEquiv_basis4 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Cl55SpinorChirality.lean:194: theorem vec55SplitEquiv_basis9 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Cl55SpinorChirality.lean:373: theorem pairedGammaProduct_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Cl55SpinorChirality.lean:945: theorem chirality55_eq_canonical [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Cl55SpinorChirality.lean:1200: theorem matrixApply_eq_mulVec [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Clifford55.lean:90: theorem e_pos_mul_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Clifford55.lean:157: theorem n_vec_null [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Clifford55.lean:160: theorem n_bar_vec_null [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Clifford55.lean:173: theorem n_vec_sq_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Clifford55.lean:312: theorem RT_swaps_semispinors [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/CliffordTower.lean:87: theorem mersenne_eq_pow_sub_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/CliffordTower.lean:96: theorem combinatorial_hierarchy_sum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/CliffordTower.lean:109: theorem tower_growth_to_seven [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/CliffordTowerFunctor.lean:44: theorem dim_Cl_pow_two [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/CliffordTowerFunctor.lean:46: theorem dim_imag_Cl_mersenne [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/CliffordTowerFunctor.lean:48: theorem dim_growth [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/CliffordTowerFunctor.lean:57: theorem cl2 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/CliffordTowerFunctor.lean:59: theorem cl3 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/ConformalGeneratorPacket55.lean:108: theorem Jgen_swaps_U_to_V [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/ConformalGeneratorPacket55.lean:112: theorem Jgen_swaps_V_to_U [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/ConformalGeneratorPacket55.lean:116: theorem Jgen_mul_neg_Jgen [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/ConformalGeneratorPacket55.lean:174: theorem T_pow_action [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/ConformalProjectiveEmbedding55.lean:56: theorem u_mul_u [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/ConformalProjectiveEmbedding55.lean:60: theorem v_mul_v [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/D4Cl11Tripotent.lean:308: theorem varlamov_pct_theorem [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/D4Cl11Tripotent.lean:314: theorem pct_preserved [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Decomposition.lean:43: lemma mem_k_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/DiscreteMoebiusGroup.lean:26: theorem moebius_T_action [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/DiscreteMoebiusGroup.lean:37: theorem moebius_S_action [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/DiscreteMoebiusGroup.lean:58: theorem monodromy_shearing_at_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/ExchangeSMatrixBridge.lean:70: theorem lowerParabolicSBlock_upper_right_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/ExchangeSMatrixBridge.lean:80: theorem lowerParabolicSBlock_equal_diagonal [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/FanoOctonionParavector.lean:45: theorem dot7_symm [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/FiniteTiltDiracShell.lean:177: theorem finiteTiltSuperCasimir_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/GogberashviliSplitOctonionBasis.lean:83: lemma zero_val [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/GogberashviliSplitOctonionBasis.lean:84: lemma addZ_val [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/GogberashviliSplitOctonionBasis.lean:85: lemma smulZ_val [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/HestenesDirac.lean:118: theorem current_eq_density_smul_velocityFrame [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/HestenesDirac.lean:187: theorem polar_current_eq_density_velocity [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/HestenesDirac.lean:192: theorem polar_spinPlane_eq_density_spinPlane [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/HestenesDirac.lean:197: theorem yvonTakabayasiAngle_of_polar_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/HestenesDirac.lean:721: theorem concrete_det_realification_eq_interval_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/HestenesDirac.lean:782: theorem concreteMajoranaBdG_det_eq_pfaffian_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/JordanWignerBridge.lean:42: theorem matStageEmbed_jw_u [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/LogCftMonodromy.lean:62: theorem jordanNilpotent_eq_parabolic_block [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/LogCftMonodromy.lean:67: theorem jordanNilpotent_eq_hypercomplex_N [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/LogCftMonodromy.lean:146: theorem virasoroL0Cell_pow [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/MatrixCompat.lean:13: lemma baseJ1_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/MonodromyFlowAdapter.lean:34: theorem infinitesimalNullGenerator_sq_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/OctonionParavectorBridge.lean:75: theorem paravectorMul_fst [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/OctonionParavectorBridge.lean:80: theorem paravectorMul_snd [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/ProjectiveCrossRatio.lean:73: theorem crossRatio_T_invariant [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/RealMod8Classification.lean:273: theorem hasRealDivisionRing_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/RealMod8Classification.lean:277: theorem hasComplexDivisionRing_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/RealMod8Classification.lean:281: theorem hasQuaternionicDivisionRing_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/STAOperators.lean:41: theorem leftMul_rightMul_commute [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/STAOperators.lean:54: theorem twoSidedOp_comp_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/STAOperators.lean:119: theorem rightSigma3_rightSigma3 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Sandbox/QuaternionPauliCommutators.lean:87: theorem comm_qI_qJ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Sandbox/QuaternionPauliCommutators.lean:90: theorem comm_qJ_qK [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Sandbox/QuaternionPauliCommutators.lean:93: theorem comm_qK_qI [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Sandbox/QuaternionPauliCommutators.lean:113: theorem anticomm_qI_qJ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Sandbox/QuaternionPauliCommutators.lean:116: theorem anticomm_qJ_qK [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Sandbox/QuaternionPauliCommutators.lean:119: theorem anticomm_qK_qI [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Sandbox/SplitQuaternionPauliCommutators.lean:281: theorem cplxI_comm_sbqI [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Sandbox/SplitQuaternionPauliCommutators.lean:284: theorem cplxI_comm_sbqJ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Sandbox/SplitQuaternionPauliCommutators.lean:287: theorem cplxI_comm_sbqK [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/Sandbox/SplitQuaternionPauliCommutators.lean:291: theorem cplxI_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/SpinorRep.lean:107: theorem gradingAtom_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/SplitBiquaternion.lean:136: theorem norm_splitConj [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/TodorovInternalSpace.lean:168: theorem mem_linearStabilizer_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/UniversalCoverLog.lean:118: theorem uLog_restrict_principal [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Clifford/UniversalCoverLog.lean:143: theorem uLog_after_winding [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Cocycle/LogarithmicOrderParameter.lean:72: theorem categoryNegativeLogDensity_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Cocycle/LogarithmicOrderParameter.lean:215: theorem negativeLogDensityOfUnits_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Cocycle/LogarithmicOrderParameter.lean:398: theorem scaledKahlerArea_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Cocycle/LogarithmicOrderParameter.lean:432: theorem gromovWittenFreeEnergy_eq_log [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Cocycle/LogarithmicOrderParameter.lean:441: theorem uniformLengthScale_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Cocycle/LogarithmicOrderParameter.lean:483: theorem gwFreeEnergy_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Cocycle/LogarithmicOrderParameter.lean:524: theorem scalarModularHamiltonian_eq_negativeLog [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Cocycle/MatrixDetExpTrace/Diagonal.lean:27: theorem complex_exp_sum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Cocycle/MatrixDetExpTrace.lean:34: theorem complex_exp_sum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Cocycle/SplitQuaternionicJacobian.lean:59: theorem splitNorm_transpose [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Cocycle/SplitQuaternionicJacobian.lean:154: theorem unitNorm_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Cocycle/SplitQuaternionicJacobian.lean:159: theorem unitNorm_ne_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Cocycle/SplitQuaternionicJacobian.lean:173: theorem unitNorm_coe_normOne [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Cocycle/SplitQuaternionicJacobian.lean:196: theorem scalarRN_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Cocycle/SplitQuaternionicJacobian.lean:236: theorem logJac4D_eq_two_logAbsSplitNorm [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Cocycle/SplitQuaternionicJacobian.lean:393: theorem leftMulLinear_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Cocycle/SplitQuaternionicJacobian.lean:402: theorem rightMulLinear_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Cocycle/SplitQuaternionicJacobian.lean:411: theorem twoSidedMulLinear_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Cocycle/SplitQuaternionicJacobian.lean:444: theorem leftMulMatrix4_mulVec_vec [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Cocycle/SplitQuaternionicJacobian.lean:529: theorem det_leftMulMatrix4_eq_norm_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Cocycle/SplitQuaternionicJacobian.lean:543: theorem det_rightMulMatrix4_eq_norm_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Codes/MajoranaStabilizerThreshold.lean:77: theorem analyticalFailureBound_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Codes/MajoranaStabilizerThreshold.lean:81: theorem analyticalFailureBound_le_threshold [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Compatibility/MathlibUpperHalfPlaneShadow.lean:66: theorem realToMathlibUHP_im [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Compatibility/MathlibUpperHalfPlaneShadow.lean:93: theorem chiralToComplex_im [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Compatibility/MathlibUpperHalfPlaneShadow.lean:145: theorem realDenomSq_pos [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Complex/BergmanKernelLocalization.lean:14: theorem localizedBergmanKernel_conj_symm [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/CondensedMatter/CliffordAtomsZ2n.lean:292: theorem local_charge_is_four_bit [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/CondensedMatter/DIIISuperfluid.lean:150: theorem phase_corrected_product_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/CondensedMatter/DIIISuperfluid.lean:157: theorem phase_corrected_product_chiral_symmetry [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/CondensedMatter/NonOrientableWeylSemimetal.lean:73: theorem oriented_pair_charge_cancels [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Convex/Bregman.lean:23: lemma bregmanDiv_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Convex/Bregman.lean:28: lemma bregmanDiv_eq_zero_of_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Convex/Bregman.lean:108: theorem bregmanThreePoint_eq_of_eq_left [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Convex/BregmanLegendreProofs.lean:21: theorem bregman_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Convex/Duality.lean:28: lemma KL_param_eq_bregman_swap [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Convex/Duality.lean:91: lemma KL_param_nonneg_of_convex_at [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Convex/InductiveBarrierOptimization.lean:42: theorem iterateUpdate_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Convex/Legendre.lean:188: lemma differentiable [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Convex/RadialLogBarrier.lean:47: theorem exp_radialTau [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Convex/RadialLogBarrier.lean:64: theorem radialBarrierEps_boundary [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Convex/RadialLogBarrier.lean:239: theorem tauBarrierEps_wall [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Convex/RadialLogBarrier.lean:244: theorem symmetricTauBarrierEps_wall [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Convex/SpinFactorHessian.lean:45: lemma spinFactor_radon_nikodym_entropy [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Core/SymmetricLie.lean:190: lemma mem_evenSubmodule_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Core/SymmetricLie.lean:194: lemma mem_oddSubmodule_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Core/SymmetricLie.lean:271: lemma even_convex [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Core/SymmetricLie.lean:276: lemma odd_convex [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Core/SymmetricLie.lean:414: lemma plusPart_add [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Core/SymmetricLie.lean:418: lemma minusPart_add [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Core/SymmetricLie.lean:422: lemma plusPart_smul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Core/SymmetricLie.lean:442: lemma convex_plusPart_image [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Core/SymmetricLie.lean:447: lemma convex_minusPart_image [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Core/SymmetricLie.lean:452: lemma convex_plusPart_preimage [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Core/SymmetricLie.lean:457: lemma convex_minusPart_preimage [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Core/SymmetricLie.lean:462: lemma decomposition [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Core/SymmetricLieGeneric.lean:79: lemma P_plus_fixed [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Dynamics/HyperbolicComponent.lean:52: theorem componentAReal_det_eq_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Dynamics/HyperbolicComponent.lean:57: theorem componentAReal_det_pos [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Dynamics/HyperbolicComponent.lean:62: theorem componentAReal_trace [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Dynamics/KanDecomposition.lean:106: theorem componentN_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Dynamics/KanDecomposition.lean:116: theorem componentN_pow [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Dynamics/KanDecomposition.lean:136: theorem componentA_det_eq_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Dynamics/KanDecomposition.lean:154: theorem kan_product_00 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Dynamics/KanDecomposition.lean:162: theorem kan_product_10 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Dynamics/KanDecomposition.lean:173: theorem kan_product_11 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Dynamics/KmsBoundary.lean:63: theorem modularHamiltonian_exp_isSelfAdjoint [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Dynamics/RapiditySpace.lean:67: theorem rapidity_upper_ray_coordinate [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Dynamics/SouriauBostConnesTheorem.lean:134: theorem quantum_dimension_tau_eq_phi [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Dynamics/SouriauDiracHodge.lean:156: theorem zero_temperature_anomaly_cancellation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Dynamics/SouriauDiracHodge.lean:388: theorem zero_temperature_anomaly_cancellation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/E8/E8TrialityThermalProtection.lean:195: theorem positive_roots_E8_add_seven_eq_127 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Eval/SorryFillerTest.lean:18: theorem add_zero_easy [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Eval/SorryFillerTest.lean:22: theorem zero_add_easy [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Eval/SorryFillerTest.lean:31: theorem add_comm_easy [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Eval/SorryFillerTest.lean:35: theorem add_assoc_easy [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Experimental/WeylCantorFock.lean:157: theorem splitDirac_zero_weight [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/ExponentialFamily/Analytic/Softmax.lean:41: lemma softmaxPartition_pos [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/ExponentialFamily/Analytic/Softmax.lean:46: lemma softmaxProb_pos [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/AffineDynkinGoutevTonev.lean:51: theorem affineNullSouriauGenerator_eq_sum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/AmariChentsovFierzTorsion.lean:43: theorem potential_eq_dikin_plus_tail [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/AmariChentsovFierzTorsion.lean:54: theorem secondJet_eq_dikin [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/AmariChentsovFierzTorsion.lean:71: theorem cubicTorsion_eq_amari_mismatch [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/AmariChentsovFierzTorsion.lean:75: theorem cubicTorsion_eq_zero_of_balanced [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/AmariChentsovFierzTorsion.lean:83: theorem jonesFierz_trace_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ArithmeticHamiltonianZeta.lean:34: theorem arithmeticEnergy_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ArithmeticHamiltonianZeta.lean:44: theorem arithmeticEnergy_pow [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ArithmeticHamiltonianZeta.lean:48: theorem arithmeticBoltzmannWeight_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ArithmeticHamiltonianZeta.lean:69: theorem finiteArithmeticTrace_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ArithmeticHamiltonianZeta.lean:74: theorem finiteZetaTrace_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ArtinParityFlow.lean:90: theorem concrete_adjacent_artin [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ArtinParityFlow.lean:94: theorem concrete_separated_artin [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/AssociativeCommutatorLie.lean:39: theorem comm_eq_zero_of_forall_commutes [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/AtomicCliffordKAN.lean:110: theorem atomicSupertrace_pure_squeeze [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BiquaternionExpClosure.lean:116: theorem trace_tracelessPauli [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BiquaternionLaplaceTripotent.lean:99: theorem scaleMatrix_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BiquaternionLaplaceTripotent.lean:104: theorem scale_det_at_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BiquaternionLaplaceTripotent.lean:107: theorem scale_det_at_neg_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BiquaternionLaplaceTripotent.lean:110: theorem scale_det_at_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BiquaternionMobiusSquashing.lean:41: theorem expCayleySquash_eq_scalarCayley [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BisoiForbiddenE1Mixing.lean:19: theorem P30_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BisoiForbiddenE1Mixing.lean:20: theorem S32_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BisoiForbiddenE1Mixing.lean:21: theorem Cl34_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BisoiForbiddenE1Mixing.lean:22: theorem Ar36_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BizzetiA67IVGMR.lean:122: theorem radial_one_body_extrapolated_eq_uniformOneBody [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BogoliubovFrameTransport.lean:84: lemma spinConnection_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BosonicPrimonPartition.lean:37: theorem bosonOccupationWeight_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BosonicPrimonPartition.lean:41: theorem bosonOccupationWeight_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BosonicPrimonPartition.lean:46: theorem singlePrimeBosonPartition_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BosonicPrimonPartition.lean:51: theorem finite_two_prime_euler_product [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BostConnesDeformation.lean:97: lemma deformedSuper_local_singleton [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BostConnesDeformation.lean:101: lemma deformedBoson_local_singleton [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BraidCliffordIntegration.lean:56: theorem artinMove_preserves_uniformCliffordAmplitude [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BraidCliffordIntegration.lean:92: theorem clifford_adjacent_artin [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BraidCliffordIntegration.lean:98: theorem clifford_separated_artin [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BraidCliffordIntegration.lean:106: theorem finiteToInfinite_castSucc [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BraidInductiveColimitCategory.lean:47: theorem generatorFromColimit_ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BraidInductiveColimitCategory.lean:78: theorem wordFromColimit_ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BraidInductiveColimitComplement.lean:40: theorem finiteSuccEmbed_val [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BraidInductiveColimitComplement.lean:44: theorem finiteToInfinite_succ_compatible [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BraidInductiveColimitComplement.lean:54: theorem finite_stage_card [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BraidInductiveColimitComplement.lean:119: theorem wordToInfinite_length [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BraidInductiveColimitComplement.lean:123: theorem wordSuccEmbed_length [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BraidedCocycleWilsonEntropy.lean:84: theorem zeroAffinity_is_cocycle [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BraidedCocycleWilsonEntropy.lean:112: theorem braidCirculationDefect12_zero_of_invariant [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BrillouinKleinNilpotentAttractor.lean:108: theorem collapsed_fixed_norm_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BuresInformationGeodesicFlow.lean:35: theorem modularFlow_zero_time [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BuresInformationGeodesicFlow.lean:76: theorem bures_center_distance_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BuresInformationGeodesicFlow.lean:82: theorem bures_metric_at_origin [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BuresMetricClosedCartography.lean:397: theorem langlands_functor_is_GNS_colimit [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/BuresMetricClosedCartography.lean:413: theorem node_render [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CARCCRCantorFock.lean:57: theorem carWord_card [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CARCCRCantorFock.lean:61: theorem ccrCutoffWord_card [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CARCCRCantorFock.lean:139: theorem ccrCutoffLocal_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CARCCRCantorFock.lean:143: theorem ccrCutoffLocal_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CARCCRCantorFock.lean:180: theorem carOrdinaryLocal_eq_bool_trace [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:93: lemma d2Map_square [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:95: theorem aeonCount_eq_three [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:97: theorem generationCount_eq_three [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:99: theorem ckmAngleCount_eq_three [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:101: theorem ckmPhaseCount_eq_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:103: theorem ckmPhysicalParameterCount_eq_four [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:105: theorem upTypeCount_eq_three [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:107: theorem downTypeCount_eq_three [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:109: theorem ckmMatrixEntryCount_eq_nine [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:111: theorem smOneGenerationWeylCount_eq_sixteen [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:113: theorem threeGenerationWeylCount_eq_fortyEight [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:115: theorem su3Rank_eq_two [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:117: theorem su3RootCount_eq_six [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:119: theorem su3CartanCount_eq_two [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:121: theorem su3GeneratorCount_eq_eight [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:123: theorem su2Rank_eq_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:125: theorem su2RootCount_eq_two [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:127: theorem su2CartanCount_eq_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:129: theorem su2GeneratorCount_eq_three [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:131: theorem u1Rank_eq_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:133: theorem smRank_eq_four [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:135: theorem smGeneratorCount_eq_twelve [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:137: theorem colorQuadraticCasimirFund_eq_four_thirds [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:139: theorem colorQuadraticCasimirAdj_eq_three [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:141: theorem weakQuadraticCasimirDoublet_eq_three_fourths [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:143: theorem weakQuadraticCasimirTriplet_eq_two [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:161: theorem identityCKM_eq_kronecker [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:185: theorem stablePage_eq_three [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:187: theorem serreResidueRank_eq_eight [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:189: theorem aeonColimitObjectCount_eq_three [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:191: theorem aeonTransitionCount_eq_two [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:193: theorem aeonColimitRank_eq_twentyFour [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:195: theorem d2Bidegree_zero_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:216: theorem edge_aeon_generates_ckm [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:219: theorem edge_ckm_mixes_three_generation_sm [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:222: theorem edge_three_generation_sm_carries_su3_color [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:225: theorem edge_three_generation_sm_carries_su2_weak [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CKMAeonColimit.lean:228: theorem edge_three_generation_sm_carries_u1_hypercharge [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CPTCausalCone.lean:16: theorem eps_sq_eq_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CPTCausalCone.lean:21: theorem J_sq_eq_neg_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CPTKreinTowerBridge.lean:131: theorem pairEmb_mirror_comm [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CanonicalSouriauPauliThermodynamics.lean:61: theorem pauliPairing_axis [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CanonicalSouriauPauliThermodynamics.lean:66: theorem pauliParavectorPairing_axis [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CanonicalSouriauPauliThermodynamics.lean:87: theorem pauliParavectorPairing_from3_with_identity [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CanonicalSouriauPauliThermodynamics.lean:93: theorem pauliPairing_single_axis [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CanonicalSouriauPauliThermodynamics.lean:98: theorem pauliLocalPartition_single_axis [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CanonicalSouriauPauliThermodynamics.lean:119: theorem pauliParavectorLocalPartition_with_identity [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CanonicalSouriauPauliThermodynamics.lean:150: theorem pauliParavectorLocalPartition_weyl [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CasimirIsospinHamiltonian.lean:52: theorem mass_casimir_stiffness [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CasimirIsospinHamiltonian.lean:82: theorem casimir_hamiltonian_linear [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CauchyHolography.lean:66: theorem mellin_shannon_preserves_metric [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ChiralCuntzInductive.lean:40: theorem chiralStep_parity_preserving [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ChiralTwistedFibration.lean:140: theorem sector_eMinus [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ChiralTwistedFibration.lean:143: theorem sector_ePlus [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CognitiveAccretionDiskSelfReferential.lean:63: theorem attentionKreinMetric_zero_left [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CompleteHolographicDictionary.lean:28: theorem mobius_parity [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CompleteHolographicDictionary.lean:102: theorem twisted_thermo_beta_independent [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ComplexTemperatureRH.lean:84: theorem gradedPrimonPartition_reciprocal [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ComplexTemperatureRH.lean:110: theorem complexTemperature_re [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ComplexTemperatureRH.lean:114: theorem complexTemperature_im [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ComplexTemperatureRH.lean:118: theorem dampingExponent_complexTemperature [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ComplexTemperatureRH.lean:122: theorem phaseFrequency_complexTemperature [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ComplexTemperatureRH.lean:126: theorem criticalBalanceLine_complexTemperature [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ComplexTemperatureRH.lean:130: theorem arithmeticPhase_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ConcreteCliffordDiracTower.lean:155: theorem cuntzDiracFinite_self_adjoint [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ConnesMarcolliShimura.lean:81: theorem milnorMorphism_eq_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ConnesMarcolliShimura.lean:86: theorem action_one_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ConnesMarcolliShimura.lean:91: theorem action_one_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ConnesMarcolliShimura.lean:101: theorem adelicShimuraCutOff_all [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ConnesMarcolliShimura.lean:120: theorem dedekindLFunction_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ConnesMarcolliShimura.lean:125: theorem dedekindLFunction_eq_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ConnesMarcolliShimura.lean:134: theorem phase_transition_at_two [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ContinuumAsColimitCounting.lean:31: theorem bitword_count [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ContinuumAsColimitCounting.lean:56: theorem fourword_count [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CriticalLineMetriplectic.lean:33: theorem entropic_dissipation_rate_eq_half [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CuntzKriegerKTheory.lean:38: theorem penrose_ktheory_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CuntzKriegerKTheory.lean:41: theorem fibonacci_ktheory_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CuntzKriegerPrimon.lean:49: theorem allowed_00 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CuntzKriegerPrimon.lean:52: theorem allowed_01 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CuntzKriegerPrimon.lean:55: theorem allowed_10 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CuntzKriegerPrimon.lean:58: theorem forbidden_11 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/CuntzKriegerPrimon.lean:85: theorem finitePrimonPartition_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/D4TrialityUniverse.lean:49: theorem cartan_is_abelian [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/DeterminantMoebiusFunctor.lean:21: theorem det_scale_nonneg [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/DeterminantMoebiusFunctor.lean:25: theorem detScale_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/DeterminantMoebiusFunctor.lean:30: theorem detParity_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/DeterminantMoebiusFunctor.lean:89: theorem moebius_duality_layer [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/DeterminantSupergrading.lean:40: theorem superGrade_id [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/DeterminantSupergrading.lean:52: theorem superGrade_chiralParity [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/DeterminantSupergrading.lean:64: theorem superGrade_modular_j [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/DeterminantSupergrading.lean:78: theorem emergentK_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/DeterminantSupergrading.lean:81: theorem superGrade_emergentK [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/DeterminantSupergrading.lean:86: theorem even_even [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/DeterminantSupergrading.lean:91: theorem even_odd [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/DeterminantSupergrading.lean:96: theorem odd_even [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/DeterminantSupergrading.lean:101: theorem odd_odd [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/DeterminantSupergrading.lean:132: theorem superTrace_vacuum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/DiracResolventZeroModeTripotent.lean:100: theorem tripScale_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/DiracResolventZeroModeTripotent.lean:105: theorem tripotent_zero_pole [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/DupontHypersurfaceOSModel.lean:65: theorem productSignExponent_eq_codim_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/EntropicHodgeDecomposition.lean:38: theorem bregman_gradient_eq_potential [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/EntropicHodgeDecomposition.lean:44: theorem gradient_field_applies_potential [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ExceptionalNonorientableTopology.lean:72: theorem klein_abelian_torsion [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ExceptionalNonorientableTopology.lean:77: theorem rp_abelian_torsion [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ExtractBraid.lean:175: lemma hc1 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ExtractBraid.lean:200: lemma hc8 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FermiLevelGap.lean:41: theorem shiftedFermiLevel_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FermiLevelGap.lean:45: theorem fermionFugacity_at_fermi [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FermiLevelGap.lean:67: theorem gap_nonnegative [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FermionicPrimonIndex.lean:65: theorem gradedIndex_singularity_iff_boson_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FermionicPrimonPartition.lean:34: theorem fermionOccupationWeight_false [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FermionicPrimonPartition.lean:38: theorem fermionOccupationWeight_true [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FermionicPrimonPartition.lean:42: theorem singlePrimeFermionPartition_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FibAnyonThm1.lean:11: lemma h5sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FibAnyonThm2.lean:11: lemma h5sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FibAnyonThm2.lean:31: lemma sqrt_ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FibAnyonThm3.lean:17: lemma starRingEnd_int [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FibonacciCliffordBridge.lean:28: lemma h5sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FibonacciCliffordBridge.lean:90: theorem tau_maps_to_tripotent [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FibonacciCliffordBridge.lean:132: theorem atomicSupertrace_pure_squeeze [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FiniteArithmeticUHFTrace.lean:71: theorem finiteArithmeticSupertrace_snoc [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FiniteArithmeticUHFTrace.lean:101: theorem occupiedInteger_cons_false [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FiniteArithmeticUHFTrace.lean:106: theorem occupiedInteger_cons_true [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FiniteArithmeticUHFTrace.lean:111: theorem occupationNumber_cons_false [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FiniteArithmeticUHFTrace.lean:120: theorem wordParity_cons_false [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FiniteDirichletOccupation.lean:58: theorem selectedWeightProduct_cons_false [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FiniteDirichletOccupation.lean:64: theorem selectedWeightProduct_cons_true [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FiniteDirichletOccupation.lean:70: theorem occupiedInteger_cons_false [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FiniteDirichletOccupation.lean:76: theorem occupiedInteger_cons_true [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FiniteDirichletOccupation.lean:105: theorem occupationNumber_cons_false [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FiniteDirichletOccupation.lean:114: theorem wordParity_cons_false [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FiniteGNSConstruction.lean:30: theorem omegaState_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FiniteGNSConstruction.lean:34: theorem omegaState_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FiniteGNSConstruction.lean:38: theorem omegaState_star_mul_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FiniteGNSConstruction.lean:57: theorem omegaState_add [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FiniteGNSConstruction.lean:62: theorem omegaState_smul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FiniteGNSConstruction.lean:70: theorem gns_expectation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FiniteGNSConstruction.lean:86: theorem pi_star_adjoint' [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FiniteMobiusCoefficient.lean:37: theorem occupationExpansion_nil [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FiniteMobiusCoefficient.lean:40: theorem occupationExpansion_cons [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FiniteMobiusCoefficient.lean:58: theorem mobiusWordCoefficient_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FiniteMobiusCoefficient.lean:62: theorem mobiusWordCoefficient_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FinitePrimeFock.lean:56: theorem ordinaryFermionTrace_nil [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FinitePrimeFock.lean:60: theorem gradedFockSupertrace_nil [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FinitePrimeFock.lean:64: theorem bosonicFockDeterminant_nil [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FinitePrimeFock.lean:68: theorem ordinaryFermionTrace_cons [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FinitePrimeFock.lean:73: theorem gradedFockSupertrace_cons [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FinitePrimeFock.lean:78: theorem bosonicFockDeterminant_cons [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FinitePrimeFock.lean:103: theorem one_mode_ordinary_trace [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FiniteUHFBooleanTrace.lean:35: theorem gradedBitSelector_false [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FiniteUHFBooleanTrace.lean:39: theorem gradedBitSelector_true [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FiniteUHFBooleanTrace.lean:43: theorem finiteBooleanTrace_nil [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FiniteUHFBooleanTrace.lean:46: theorem finiteBooleanTrace_cons [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FixedLineRiemannKlein.lean:70: theorem pgPhase_odd [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FockSpaceDerivation.lean:38: theorem bosonic_commutation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FreedHeteroticTorsion.lean:12: theorem vanishing_global_holonomy [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FureyLadderSerreResidues.lean:18: lemma d2ZeroModule_finrank_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FureyLadderSerreResidues.lean:28: lemma nilpotentSquare_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FureyLadderSerreResidues.lean:246: lemma serre_d2_extracts_furey_ladder_residue [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FureyLadderSerreResidues.lean:250: lemma furey_ladder_residue_generates_su3_color [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FureyLadderSerreResidues.lean:254: lemma furey_ladder_residue_generates_su2_weak [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FureyLadderSerreResidues.lean:258: lemma furey_ladder_residue_generates_u1_hypercharge [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/FureyLadderSerreResidues.lean:262: lemma sm_one_generation_carries_furey_ladder_residue [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/GNSModularObservables.lean:33: theorem normalizedTrace_sigma3 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/GNSModularObservables.lean:37: theorem normalizedTrace_identity [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/GeometricZeta.lean:53: theorem geometricGradedIndexPole_iff_denominator_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/GeometricZeta.lean:66: theorem geometric_paravector_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/GeometricZeta.lean:81: theorem riemann_zeros_are_lightcones [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/GlideDiracSelectionRule.lean:26: theorem pgPhase_odd [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/GlideDiracSelectionRule.lean:30: theorem pgPhase_even [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/GohbergKreinIndex.lean:74: theorem cw_liftedQuarterSum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/GohbergKreinIndex.lean:82: theorem finiteGKIndex_cwLoop [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/GoldenCCR.lean:54: theorem exp_neg_penroseBeta [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/GoldenCCR.lean:58: theorem qPenrose_eq_thickFreq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/GoldenCCR.lean:76: theorem golden_exchange_relation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/GoutevTonevPrinciple.lean:146: theorem readout_comp_operator [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/GrandCanonicalBerezinian.lean:90: theorem gcBerezinian_local_cayley [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/GrandCanonicalPrimon.lean:58: theorem gcShiftedEnergy_at_fermi [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/GrandCanonicalPrimon.lean:62: theorem gcFugacity_at_fermi [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/GrandCanonicalPrimon.lean:88: theorem gcGappedFugacity_zero_gap_at_fermi [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/GrandCanonicalPrimon.lean:107: theorem gcBosonTruncatedPartition_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/GrandCanonicalPrimon.lean:111: theorem gcBosonTruncatedPartition_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/GrandCanonicalPrimon.lean:143: theorem gcBosonTwoModeProduct [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/GrandHolographicTheorem.lean:63: theorem Jep_det_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/GrandHolographicTheorem.lean:112: theorem clifford55_index_cancel [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/GrandHolographicTheorem.lean:114: theorem clifford55_dimension [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/GrandUnifiedVacuum.lean:6: theorem pin55_decomposition [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/GrandUnifiedVacuum.lean:12: theorem modular_hamiltonian_is_boltzmann_entropy [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/GuptaAdaptVQERandomHamiltonians.lean:71: theorem one_Y_is_time_reversal_allowed [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/GuptaAdaptVQERandomHamiltonians.lean:99: theorem adapt_gradient_zero_when_commutator_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/GuptaAdaptVQERandomHamiltonians.lean:105: theorem relative_error_zero_for_exact_match [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/HestenesKreinColimitBridge.lean:76: theorem mirrorUnit_rotorUnit_neg [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/HolographicMonodromy.lean:16: theorem conformal_flow_eq_monodromy [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/HurwitzTwistedSector.lean:238: theorem finiteHurwitzCharacterCombination_add [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/HurwitzTwistedSector.lean:245: theorem finiteHurwitzCharacterCombination_smul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/IwasawaKUnification.lean:74: theorem iwasawa_trace_annihilation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/JaynesFiniteSetsColimitBridge.lean:156: theorem finiteEntropy_const_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/JaynesFiniteSetsColimitBridge.lean:161: theorem continuousEntropy_const_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/KANFormalization.lean:25: theorem det_total [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/KANFormalization.lean:30: theorem det_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/KANTraceSectorization.lean:22: lemma determinantScale_nonneg [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/KANTraceSectorization.lean:138: theorem nilpotentGenerator_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/KANTraceSectorization.lean:147: theorem compactGenerator_trace_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/KANTraceSectorization.lean:151: theorem noncompactGenerator_trace_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/KANTraceSectorization.lean:155: theorem nilpotentGenerator_trace_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/KANTraceSectorization.lean:263: theorem nilpotentGenerator_isNilpotent [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/KaneMeleOrbifold.lean:32: theorem nontrivial_phase_is_nonorientable [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/KanekoA67HighSpinMED.lean:20: theorem MED_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/KasparovKreinCategory.lean:76: theorem kkBoundaryPairing_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/KasparovKreinDoubling.lean:34: theorem bdg_trace_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/KleinBottle.lean:63: theorem mirror_fixed_points [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/KleinBottle.lean:67: theorem mirror_involution [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/KleinBottle.lean:72: theorem cone_point_origin [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/KleinBottle.lean:76: theorem half_turn_involution [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/KleinBottle.lean:81: theorem glide_is_mirror_translated [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/KleinBottle.lean:101: theorem mirror_orientation_reversing [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/KleinBottle.lean:104: theorem cone_point_orientation_preserving [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/KleinBottle.lean:107: theorem glide_orientation_reversing [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/KleinBottleCobordism.lean:55: theorem vacuum_is_defect_free [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/KleinGeometrySupergraded.lean:22: theorem translation_parity_even [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/KleinGeometrySupergraded.lean:29: theorem glide_parity_odd [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/KleinGeometrySupergraded.lean:33: theorem composition_parity_is_supergraded [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/KleinParafermionCohomology.lean:100: theorem sectorOfHolonomy_boson [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/KreinDeterminantAnalyticity.lean:109: lemma traceZeroGenerator_trace [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/KreinMoorePenrose.lean:114: theorem dikin_ignores_harmonic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/LECM2022ElectroweakRadiiISB.lean:58: theorem ckm_unitarity_zero_defect [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/LECM2022ElectroweakRadiiISB.lean:101: theorem exact_isospin_combined_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/LECM2022ElectroweakRadiiISB.lean:105: theorem exact_isospin_deviation_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/LECM2022ElectroweakRadiiISB.lean:156: theorem superallowed_beta_decay_constrains_ckm_first_row_unitarity [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/LECM2022ElectroweakRadiiISB.lean:160: theorem deltaC_corrects_superallowed_beta_decay [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/LECM2022ElectroweakRadiiISB.lean:164: theorem electroweak_nuclear_radii_probe_deltaC [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/LECM2022ElectroweakRadiiISB.lean:168: theorem isovector_monopole_measures_electroweak_nuclear_radii [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/LQGProblemsResolvedByChiralFramework.lean:181: theorem kantorTriple_symm [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/LQGProblemsResolvedByChiralFramework.lean:247: theorem volume_from_wigner_dyson [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/LieFlowCompilerBridge.lean:55: lemma trajectory_end [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/LieFlowMatching.lean:39: theorem geodesicPoint_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/LieFlowMatching.lean:64: theorem sampleLoss_eq_zero_if_perfect [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/LieFlowMatching.lean:95: theorem scheduledSampleLoss_eq_zero_if_perfect [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/LogDetSuperKahlerBarrier.lean:28: theorem diagState_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/LogDetSuperKahlerBarrier.lean:57: theorem Znil_det_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/MITFInvariant.lean:76: lemma partialNumeratorsProd_succ_some [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/MITFInvariant.lean:82: lemma det_stepMatrix [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/MITFOrientability.lean:52: theorem Sminus_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/MITFOrientabilityFlow.lean:44: theorem Sminus_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/Matrix2KANPauliChain.lean:83: theorem mat2_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/Matrix2KANPauliChain.lean:112: theorem traceful_add_traceless [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/Matrix2KANPauliChain.lean:138: theorem traceless_pauli_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/Matrix2KANPauliChain.lean:154: theorem NPart_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/Matrix2KANPauliChain.lean:158: theorem KANMatrix_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/Matrix2KANPauliChain.lean:163: theorem kLog_trace [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/Matrix2KANPauliChain.lean:164: theorem aLog_trace [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/Matrix2KANPauliChain.lean:165: theorem nLog_trace [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/MaxCalFeynmanGaussBonnet.lean:25: theorem max_cal_feynman_iso [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/MellinWaveletScaleShiftDigest.lean:83: theorem log_mul_as_add [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/MetriplecticCausality.lean:27: theorem flow_timelike [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/MetriplecticCausality.lean:33: theorem flow_null [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/MetriplecticCausality.lean:39: theorem cauchy_surface_measure_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/MobiusInversion.lean:39: theorem mobius_is_dirichlet_inverse [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/MobiusInversion.lean:43: theorem mobius_inverse_left [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/MobiusWittenKleinIndex.lean:39: theorem pgPhase_odd [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:118: theorem aeonCount_eq_three [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:120: theorem generationCount_eq_three [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:122: theorem vintageCount_eq_three [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:124: theorem modularTransitionCount_eq_two [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:126: theorem stablePage_eq_three [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:128: theorem serreResidueRank_eq_eight [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:130: theorem aeonColimitRank_eq_twenty_four [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:132: theorem threeGenerationWeylCount_eq_forty_eight [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:134: theorem su3Rank_eq_two [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:136: theorem su3GeneratorCount_eq_eight [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:138: theorem su2Rank_eq_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:140: theorem su2GeneratorCount_eq_three [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:142: theorem u1Rank_eq_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:144: theorem smRank_eq_four [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:146: theorem smGeneratorCount_eq_twelve [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:148: theorem cartanGeneratorCount_eq_four [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:150: theorem colorQuadraticCasimirFund_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:152: theorem weakQuadraticCasimirDoublet_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:154: theorem colorQuadraticCasimirAdj_eq_three [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:156: theorem weakQuadraticCasimirTriplet_eq_two [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:158: theorem vintageIndex_must_eq_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:160: theorem vintageIndex_vintage_eq_two [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:162: theorem vintageIndex_reserve_eq_three [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:164: theorem generationIndex_g1_eq_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:166: theorem generationIndex_g2_eq_two [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:168: theorem generationIndex_g3_eq_three [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:170: theorem flavorGeneration_up_eq_g1 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:172: theorem flavorGeneration_charm_eq_g2 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:174: theorem flavorGeneration_top_eq_g3 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:176: theorem qDial_eq_one_tenth [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:187: theorem inverseAgingWeight_one_eq_ten [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:189: theorem inverseAgingWeight_two_eq_hundred [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:191: theorem inverseAgingWeight_three_eq_thousand [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:202: theorem moebiusTwist_involutive [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:205: theorem modularRoundTrip_eq_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:208: theorem agingOrbit_zero_eq_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:211: theorem agingOrbit_one_eq_neg [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:214: theorem agingOrbit_two_eq_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:217: theorem d2Bidegree_zero_one_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:219: theorem d2Bidegree_two_one_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:221: theorem ckmAngleCount_eq_three [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:223: theorem ckmPhaseCount_eq_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:225: theorem ckmPhysicalParameterCount_eq_four [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:227: theorem ckmMatrixEntryCount_eq_nine [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:229: theorem determinantIdentityValue_eq_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:260: theorem edgeHolds_modular_aging_operator_iterates_aeon_colimit [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:263: theorem edgeHolds_aeon_colimit_refines_generation_flavor [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:266: theorem edgeHolds_generation_flavor_generates_ckm_matrix [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularAgingFlavor.lean:269: theorem edgeHolds_generation_flavor_carries_sm_symmetry [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModularKreinReflectionColimit.lean:52: theorem embIter_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModuleCatCohomology.lean:74: theorem trivialExteriorPowerComplex_object_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ModuleCatCohomology.lean:79: theorem trivialExteriorPowerComplex_d_squared [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/MorandiWallpaperCohomology.lean:85: theorem actionCase_count [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/MorandiWallpaperCohomology.lean:92: theorem totalExtensionClasses_eq_18 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/MorandiWallpaperCohomology.lean:99: theorem morandiWallpaperCount_eq_17 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/NonHermitianKitaevCuntzChain.lean:47: theorem chiralBlock_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/NonHermitianKitaevCuntzChain.lean:91: theorem cuntzShiftBlock_det_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/NonIsoConf3DeRhamCohomologyFormula.lean:49: theorem deRhamBranchPoincare_product_formula [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/NonIsoConf3DeRhamCohomologyFormula.lean:57: theorem deRhamBranchPoincare_os_formula [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/NonIsoConf3DeRhamCohomologyFormula.lean:64: theorem lightConeProduct_rank_at_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/NonIsoConf3DeRhamCohomologyFormula.lean:69: theorem lightConeOS_rank_at_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/NonIsoConf3DeRhamCohomologyFormula.lean:85: theorem lightConeRankGap_at_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/NonIsoConf3DupontGysinModel.lean:248: theorem collapse12_external_edges_identified [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/NonIsoConf3LogCFTPotential.lean:101: theorem logPotentialBranchChoice_product [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/NonIsoConf3LogCFTPotential.lean:105: theorem logPotentialBranchChoice_osAlpha [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/NonIsoConf3QuadricD4Model.lean:38: theorem alpha_degrees [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/NonIsoConf3QuadricD4Model.lean:109: theorem top_candidate_rank_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/NonOrientableBraid.lean:34: theorem rp2_charge_eq_active [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/NonOrientableBraid.lean:38: theorem active_klein_word_def [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/NoncommutativeTilingAlgebra.lean:31: theorem conv_assoc [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/NoncommutativeTilingAlgebra.lean:238: theorem allOnesCK_rhs [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/NoncommutativeTilingAlgebra.lean:247: theorem allOnesCK_two_rhs [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/NuclearPhononGenerators.lean:150: theorem quadrupole_phonon_is_u6_generator [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/OakuTakayamaDModuleDeRham.lean:77: theorem introBPolynomial_root_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/OakuTakayamaDModuleDeRham.lean:106: theorem introFourierNormalForm_xd2 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/OpticalAndreevSpinor.lean:86: theorem halfWavePlate_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/OpticalAndreevSpinor.lean:112: theorem axialSelfHamiltonian_trace_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PRL124RuPairingSymmetry.lean:105: theorem isSelfConjugate_eq_true [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PRL124RuPairingSymmetry.lean:144: theorem isovectorPairT_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PRL124RuPairingSymmetry.lean:147: theorem isovectorPairI_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PRL124RuPairingSymmetry.lean:150: theorem isoscalarPairT_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PRL124RuPairingSymmetry.lean:153: theorem isoscalarPairMinimalI_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PartitionPoleCriterion.lean:97: theorem zeta_critical_rate [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PartitionPoleCriterion.lean:101: theorem zeta_pole_model_inverse [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PauliZornTrifactor.lean:54: theorem detSector_positive [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PauliZornTrifactor.lean:140: theorem zornDet_pureUpper [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PauliZornTrifactor.lean:144: theorem zornDet_pureLower [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PenroseArithmetic.lean:113: theorem phiAdicDistance_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PenroseArithmetic.lean:138: theorem inflationEnergy_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PenroseArithmetic.lean:141: theorem goldenPrimeClass_five [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PenroseArithmetic.lean:145: theorem goldenPrimeClass_split_11 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PenroseArithmetic.lean:149: theorem goldenPrimeClass_split_19 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PenroseArithmetic.lean:153: theorem goldenPrimeClass_inert_3 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PenroseArithmetic.lean:157: theorem goldenPrimeClass_inert_13 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PenroseArithmetic.lean:161: theorem goldenMul_phi_phi [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PenroseCuntzKriegerHolography.lean:24: theorem M_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PenroseCuntzKriegerHolography.lean:26: theorem B_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PentagonPenroseWallpaperFractal.lean:27: theorem pentagon_forbidden_wallpaper [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PentagonPenroseWallpaperFractal.lean:52: theorem thick_substitution [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PentagonPenroseWallpaperFractal.lean:55: theorem thin_substitution [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PoissonGaussianGNSColimit.lean:80: theorem poissonPMF_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PoissonGaussianGNSColimit.lean:123: theorem standardizedPoissonCoordinate_eq_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PoissonGaussianGNSColimit.lean:129: theorem gaussianPDF_center [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PoissonGaussianGNSColimit.lean:147: theorem poissonNormalApproximation_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PoissonGaussianGNSColimit.lean:208: theorem algebraInclusion_castSucc [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PoissonGaussianGNSColimit.lean:219: theorem localPoissonState_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PoissonGaussianGNSColimit.lean:240: theorem finiteSpectrumEmbedding_apply_of_lt [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PoissonGaussianGNSColimit.lean:245: theorem finiteSpectrumEmbedding_apply_of_not_lt [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PoissonGaussianGNSColimit.lean:276: theorem finiteVacuumVector_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PoissonGaussianGNSColimit.lean:280: theorem gnsColimitVacuum_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PrimaMateriaInformationGeometry.lean:31: lemma probability_density_nonneg [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PrimeMellinSymplecticCAR.lean:45: lemma det_doubledLift [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PrimonBosonFermionDuality.lean:60: theorem mobius_zero_at_hagedorn [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PrimonCuntzTower.lean:98: theorem cuntzRangeProjection_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PrimonCuntzTower.lean:165: theorem stageToSequence_apply_of_le [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PrimonCuntzTower.lean:169: theorem stageToSequence_apply_of_not_le [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PrimonHilbertPolyaSeparation.lean:44: theorem primeCrystalPotentialCoeff_eq_primeEnergy [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PrimonSuperThermodynamics.lean:34: lemma super_partition_singleton [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PrimonSuperThermodynamics.lean:38: lemma boson_partition_singleton [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PrimonSuperThermodynamics.lean:42: lemma super_internal_singleton [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PrimonSuperThermodynamics.lean:46: lemma boson_internal_singleton [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PrimonSuperThermodynamics.lean:50: lemma super_free_singleton [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PrimonSuperThermodynamics.lean:54: lemma boson_free_singleton [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PrimonSuperThermodynamics.lean:58: lemma super_entropy_singleton [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PrimonSuperThermodynamics.lean:62: lemma boson_entropy_singleton [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PrimonSuperThermodynamics.lean:95: lemma freeEnergy_neg_bosonic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PrimonSuperThermodynamics.lean:99: lemma internalEnergy_neg_bosonic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PrimonSuperThermodynamics.lean:255: lemma cptSpectralMap_involutive [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PrimonZetaMobius.lean:34: theorem fermion_parity_of_not_squarefree [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PrimonZetaMobius.lean:38: theorem fermion_parity_of_squarefree [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PrimonZetaMobius.lean:42: theorem fermion_parity_prime [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PrimonZetaMobius.lean:46: theorem zeta_mobius_vacuum_cancellation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/PrimonZetaMobius.lean:50: theorem mobius_zeta_vacuum_cancellation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ProjectiveCrystalKappa.lean:65: theorem halfShiftPhase_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ProjectiveCrystalSymmetry.lean:87: theorem halfReciprocalShiftPhase_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ProjectiveCuntzToeplitzCARCCR.lean:109: theorem qCCR_zero_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ProjectiveKappaKleinMobius.lean:64: theorem halfShiftPhase_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ProjectiveMobiusMatrix.lean:46: theorem mobiusMatrix_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/QCDConfinementISDivergence.lean:21: theorem windingNumber_eq_loopIndex [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/QCDConfinementISDivergence.lean:25: theorem nontrivial_winding_is_nonzero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/RelativisticBiquaternionKAN.lean:71: theorem Aboost_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/RelativisticBiquaternionKAN.lean:98: theorem spinBoostClosed_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/RescaledPhaseVolumeCanonical.lean:28: theorem commA_rescale [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/RiemannHypothesis.lean:61: theorem rhComplexTemperature_re [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/RiemannHypothesis.lean:65: theorem rhComplexTemperature_im [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/RiemannHypothesis.lean:69: theorem rhCriticalLine_complexTemperature [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/RiemannHypothesis.lean:73: theorem rhArithmeticPhase_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/S3ColorSpinorDecomposition.lean:21: theorem singlet_lane_invariant [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/S3ColorSpinorDecomposition.lean:26: theorem color_triplet_stable [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SO55NullSU5KleinSpectral.lean:82: theorem involution_square_identity [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SO55NullSU5KleinSpectral.lean:135: theorem edgeHolds_so55_null_basis_decomposes_to_su5_adjoint_24 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SO55NullSU5KleinSpectral.lean:138: theorem edgeHolds_so55_null_basis_trace_splits_to_dilaton_line_1 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SO55NullSU5KleinSpectral.lean:141: theorem edgeHolds_so55_null_basis_skew_splits_to_fermion_ten_b [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SO55NullSU5KleinSpectral.lean:144: theorem edgeHolds_so55_null_basis_skew_splits_to_fermion_tenbar_c [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SO55NullSU5KleinSpectral.lean:147: theorem edgeHolds_spinor_exterior_16_quotients_modes_klein_mobius_spectral_quotient [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SUNLoopBraidCuntzBoundary.lean:110: theorem loopBracket_matrixLoopMode [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SarkarTwoLevelIsospinMixing.lean:54: theorem H12sq_zero_at_unmixed [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SarsArangoBridge.lean:84: theorem isabelle_sigma_skew_maps_to_weyl_concept [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SarsArangoBridge.lean:89: theorem lean_weyl_system_formalizes_weyl_concept [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SarsChiralMassDilaton.lean:49: theorem localMass_zero_base [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SarsChiralMassDilaton.lean:65: theorem restoringForce_hooke [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SarsGNSFronsdalJoseph.lean:58: theorem fronsdal_relation_refl [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SarsSKMajoranaSYK.lean:158: theorem quantum_sk_has_pool_size_edge [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SarsSKMajoranaSYK.lean:162: theorem syk_has_pool_size_edge [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SarsSKMajoranaSYK.lean:166: theorem syk_embeds_by_jordan_wigner_edge [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SarsSKMajoranaSYK.lean:170: theorem jordan_wigner_realizes_cl55_block_edge [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SarsSKMajoranaSYK.lean:174: theorem syk_has_dla_dimension_edge [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SarsSU5Cl55Supertrace.lean:91: theorem odd_odd_superbracket_lands_even [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SarsWeylColimit.lean:105: theorem block_dim_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SarsWeylColimit.lean:108: theorem block_dim_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SerreSpectralSplitOctonion.lean:130: theorem differential_square_rank_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SerreSpectralSplitOctonion.lean:137: theorem e_infinity_rank_eq_e2_rank [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SheikhIsospinSymmetryBreaking.lean:13: theorem twoTz_self_conjugate [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SheikhIsospinSymmetryBreaking.lean:16: theorem Tz_self_conjugate [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SolderingForms.lean:117: theorem solder_coord_t_of_solder [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SolderingForms.lean:121: theorem solder_coord_x_of_solder [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SolderingForms.lean:132: theorem solder_coord_y_of_solder [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SolderingForms.lean:143: theorem solder_coord_z_of_solder [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SolovievQPNMChiralCuntz.lean:173: theorem coincidenceGram_eq_AadjA [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SouriauCasimirEntropyLeaves.lean:80: theorem dilation_spring_stiffness_massSq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SouriauComplexTemperature.lean:58: theorem complexTemperature_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SouriauComplexTemperature.lean:61: theorem complexTemperature_betaDirection [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SouriauComplexTemperature.lean:65: theorem complexTemperature_phaseDirection [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SouriauComplexTemperature.lean:84: theorem riemannSphereChart_some [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SouriauComplexTemperature.lean:87: theorem riemannSphereChart_none [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SouriauComplexTemperature.lean:90: theorem souriauModularExp_zero_eps [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SouriauComplexTemperature.lean:94: theorem souriauModularExp_zero_K [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SouriauComplexTemperature.lean:128: theorem complexMasterDensity_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SouriauHestenesKrein.lean:106: theorem det_sectorTripotentOperator [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SouriauHestenesKrein.lean:110: theorem sectorTripotent_positive [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SouriauHestenesKrein.lean:114: theorem sectorTripotent_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SouriauHestenesKrein.lean:118: theorem sectorTripotent_negative [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SouriauHestenesKrein.lean:127: theorem gradedSupertracePole_iff_denominator_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SouriauHestenesMobiusPole.lean:98: theorem detSector_positive [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SouriauHestenesMobiusPole.lean:148: theorem reciprocalPoleCandidate_iff_zeta_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SouriauOperatorThermodynamics.lean:81: theorem boltzmannEntropy_eq_expect_energy_add_potential [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SouriauThermoColimit.lean:128: theorem souriauStatePartition_elliptic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SouriauThermoColimit.lean:134: theorem souriauStatePartition_parabolic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SouriauThermoColimit.lean:140: theorem souriauStatePartition_hyperbolic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SouriauThermoColimit.lean:146: theorem finite_one_mode_graded [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SouriauThermoColimit.lean:186: lemma SouriauEmbed_lt [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SouriauThermoColimit.lean:191: lemma SouriauEmbed_new [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SouriauThermoColimit.lean:321: theorem paravectorTemperature_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SpacetimeGUEIsomorphism.lean:456: theorem nuclearSpacing_is_spatialDiameter [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SplitOctonionBraidSU3.lean:145: theorem nullVector_norm_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SplitOctonionMinkowski.lean:131: theorem spinBoost_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SplitOctonionNilpotent.lean:60: theorem Z_mode_null [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/StrongCPAeonTheta.lean:180: lemma cpTwiceTheta_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/StrongCPAeonTheta.lean:183: lemma thetaCancelled_eq_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/StrongCPAeonTheta.lean:238: lemma thirdAeonSediment_generates_thetaVacuum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/StrongCPAeonTheta.lean:242: lemma thetaVacuum_carries_su3Color [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/StrongCPAeonTheta.lean:246: lemma cpTwist_flips_thetaVacuum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/StrongCPAeonTheta.lean:250: lemma axionCounterterm_cancels_thetaVacuum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SuperBerezinianKlein.lean:83: theorem superBerezinian1_no_mixing [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SuperPartitionBerezinian.lean:44: theorem superPartitionRatio_eq_cayley [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SuperPartitionBerezinian.lean:48: theorem superPartitionRatio_eq_berezinian [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SuperPartitionBerezinian.lean:73: theorem exponentialCayleyPartition_eq_berezinian [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SuperPartitionBerezinian.lean:78: theorem exponential_chart_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SymbolicFockLane.lean:43: theorem occupationLane_empty [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SymbolicFockLane.lean:47: theorem occupationLane_occupied [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SymbolicFockLane.lean:51: theorem parityLane_empty [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SymbolicFockLane.lean:84: theorem ordinary_projected_local_factor [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SymbolicFockLane.lean:96: theorem two_lane_ordinary_projection [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SymbolicLaneUHFBridge.lean:51: theorem occupationLane_empty [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SymbolicLaneUHFBridge.lean:55: theorem occupationLane_occupied [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SymbolicLaneUHFBridge.lean:59: theorem parityLane_empty [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/SymbolicLaneUHFBridge.lean:67: theorem gradedLane_empty [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/T5Z2AnomalyCancellation.lean:20: theorem anomaly_cancellation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/TestTL.lean:23: lemma TL_e_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ThesisMaster.lean:92: theorem klein_fixed_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/TraceSeparationFlow.lean:22: theorem traceSector_trace [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/TraceSeparationFlow.lean:27: theorem tracelessSector_trace [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/TraceSeparationFlow.lean:32: theorem trace_decomposition [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/TransferMatrixScattering.lean:53: theorem berryConnection_trace_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/TransferMatrixScattering.lean:68: theorem scattering_transmissions_equal_of_det_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/TripotentCliffordColimit.lean:40: theorem compact_square_sign [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/TripotentCliffordColimit.lean:68: theorem nullVector_norm_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/TripotentPenroseHolography.lean:31: theorem penrose_trace [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/TwistedOrbifoldVacuum.lean:11: theorem riemann_zeroes_are_twistor_singularities [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/TwistedOrbifoldVacuum.lean:14: theorem vacuum_topology_is_twisted_k_theory [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/UHFInductiveColimit.lean:44: theorem diagEmbedSucc_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/UHFInductiveColimit.lean:92: theorem cylinder_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/UthayakumaarMirrorKnockout.lean:52: theorem MED_ground_normalized [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/V4_test2.lean:1: theorem R_P_sq_test [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/VacuumJonesKleinBirefringence.lean:34: theorem vacuumJonesTensor_birefringence [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/VacuumJonesKleinBirefringence.lean:41: theorem vacuumJonesTensor_optical_activity_upper [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/VacuumJonesKleinBirefringence.lean:46: theorem vacuumJonesTensor_optical_activity_lower [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/VacuumTopology.lean:32: lemma vacuum_is_left_identity [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/VacuumTopology.lean:36: lemma vacuum_is_right_identity [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/VacuumTopology.lean:65: lemma vacuum_is_absorbing [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/VacuumTopology.lean:85: lemma vacuum_is_contractible [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/VacuumTopology.lean:115: theorem vacuum_monodromy_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/VarlamovKleinSpectral.lean:101: theorem mobius_involutive [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/VarlamovKleinSpectral.lean:123: theorem su5_adjoint_has_weyl_a4_symmetry [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/VarlamovKleinSpectral.lean:127: theorem witten_moebius_index_splits_into_varlamov_even_spinor [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/VarlamovKleinSpectral.lean:132: theorem witten_moebius_index_splits_into_varlamov_odd_spinor [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/VarlamovKleinSpectral.lean:137: theorem witten_moebius_index_cancels_to_klein_brillouin_quotient [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/VarlamovKleinSpectral.lean:142: theorem klein_brillouin_quotient_quotients_by_tripotent_spectrum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/WallpaperBulkAnyonProjection.lean:60: theorem glide_wrap_conjugates_charge [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/WallpaperFermionSuperconductingGap.lean:54: theorem full_gap_table [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/WallpaperFermionSuperconductingGap.lean:59: theorem point_node_table [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/WallpaperMetamaterialDataset.lean:27: theorem wallpaperGroups_length [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/WallpaperMetamaterialDataset.lean:34: theorem glideGroups_length [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/WallpaperMetamaterialDataset.lean:111: theorem F_P_same_rank [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/WallpaperSemidirectProduct.lean:23: theorem pure_translation_right [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/WallpaperSemidirectProduct.lean:63: theorem point_projection_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/WarehamNullBasis55.lean:52: theorem e_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/WarehamNullBasis55.lean:53: theorem ebar_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/WarehamNullBasis55.lean:54: theorem e_orth_ebar [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/WarehamNullBasis55.lean:56: theorem n_null [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/WarehamNullBasis55.lean:57: theorem nbar_null [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/WarehamNullBasis55.lean:58: theorem n_dot_nbar [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/WarehamNullBasis55.lean:65: theorem nAt0_null [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/WarehamNullBasis55.lean:66: theorem nAt1_null [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/WarehamNullBasis55.lean:67: theorem nAt2_null [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/WarehamNullBasis55.lean:68: theorem nAt3_null [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/WarehamNullBasis55.lean:69: theorem nAt4_null [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/WarehamNullBasis55.lean:71: theorem nbarAt0_null [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/WarehamNullBasis55.lean:72: theorem nbarAt1_null [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/WarehamNullBasis55.lean:73: theorem nbarAt2_null [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/WarehamNullBasis55.lean:74: theorem nbarAt3_null [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/WarehamNullBasis55.lean:75: theorem nbarAt4_null [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/WarehamNullBasis55.lean:77: theorem nColl_null [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/WarehamNullBasis55.lean:78: theorem nbarColl_null [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/WaveguideEPBraidSpec.lean:69: theorem artin_protocol_lengths_equal [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/YanevaPd94PnSymmetry.lean:304: theorem edge_pd94_member_isospin_T1 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/YanevaPd94PnSymmetry.lean:308: theorem edge_ag94_member_isospin_T1 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/YanevaPd94PnSymmetry.lean:312: theorem edge_pd94_has_g9_2_shell [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/YanevaPd94PnSymmetry.lean:316: theorem edge_g9_2_has_isoscalar_T0 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/YanevaPd94PnSymmetry.lean:320: theorem edge_g9_2_has_isovector_T1 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/YanevaPd94PnSymmetry.lean:324: theorem edge_isoscalar_T0_competes_isovector_T1 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/YangBaxterQuotientDescent.lean:36: lemma descended_agree_on_generators [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZetaCoordinateSymmetry.lean:148: theorem chartCriticalLine_iff_complexCriticalLine [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZetaCoordinateSymmetry.lean:165: theorem centeredSigma_chartConjugation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZetaCoordinateSymmetry.lean:504: theorem criticalTangent_idempotent [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZetaCoordinateSymmetry.lean:509: theorem criticalNormal_idempotent [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZetaCoordinateSymmetry.lean:514: theorem criticalNormal_after_tangent [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZetaCoordinateSymmetry.lean:519: theorem criticalTangent_after_normal [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZetaCoordinateSymmetry.lean:535: theorem conjugation_preserves_flatQuadratic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZetaCoordinateSymmetry.lean:540: theorem functionalDual_preserves_flatQuadratic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZetaCoordinateSymmetry.lean:545: theorem criticalMirror_preserves_flatQuadratic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZetaCoordinateSymmetry.lean:565: theorem invariantPotential_opposite_normal_values [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZetaCoordinateSymmetry.lean:606: theorem normalQuadraticPotential_criticalMirror [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZetaCoordinateSymmetry.lean:611: theorem normalQuadraticPotential_eq_zero_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZetaCoordinateSymmetry.lean:620: theorem heightTranslation_preserves_u [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZetaCoordinateSymmetry.lean:630: theorem criticalMirror_commutes_heightTranslation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZetaCoordinateSymmetry.lean:639: theorem heightTranslation_preserves_flatDisplacement [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZetaCoordinateSymmetry.lean:673: theorem heightSouriauMoment_equivariance [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZetaCoordinateSymmetry.lean:679: theorem normalQuadraticPotential_heightTranslation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZetaSpectralBridge.lean:59: theorem finitePrimonMellinTrace_eq_dirichlet [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZetaSpectralBridge.lean:64: theorem finitePrimonHeatTrace_eq_mellin [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZornAssociatorSplitOctonion.lean:121: theorem dot_e [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZornAssociatorSplitOctonion.lean:125: theorem dot_e [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZornAssociatorSplitOctonion.lean:129: theorem dot_e [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZornAssociatorSplitOctonion.lean:188: theorem zornDet_Eplus [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZornAssociatorSplitOctonion.lean:192: theorem zornDet_Eminus [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZornBraidScalingCovariance.lean:61: theorem leftRegularMatrix_Q_k [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZornBraidScalingCovariance.lean:66: theorem leftRegularMatrix_R_k [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZornBraidScalingCovariance.lean:166: theorem scaledZornPhi_conjugate [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZornOPParavector.lean:127: theorem Eplus_det_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZornOPParavector.lean:131: theorem Eminus_det_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZornOPParavector.lean:159: theorem Nup_det_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZornOPParavector.lean:163: theorem Ndown_det_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/ZornParavectorNullspace.lean:79: theorem collapsed_state_norm_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/clifford_seed.lean:58: lemma cl11_to_M2_e1 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/clifford_seed.lean:59: lemma cl11_to_M2_e2 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/determinant_weyl_gauge.lean:146: theorem sector_hyperbolicChart [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/determinant_weyl_gauge.lean:150: theorem sector_ellipticChart [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/determinant_weyl_gauge.lean:154: theorem sector_nullProjector [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/determinant_weyl_gauge.lean:157: theorem sector_nilpotentN [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/determinant_weyl_gauge.lean:173: theorem det_T [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/determinant_weyl_gauge.lean:216: theorem fvolume_smul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/determinant_weyl_gauge.lean:220: theorem fvolume_weylLieFlow [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/determinant_weyl_gauge.lean:224: theorem fvolume_weylLieFlow_vacuum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/determinant_weyl_gauge.lean:228: theorem weylFlow_zero_lightcone [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/determinant_weyl_gauge.lean:245: theorem negLogDet_weylLieFlow_vacuum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/determinant_weyl_gauge.lean:325: theorem boltzmannDegeneracy_weylFlow_vacuum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/inductive_colimit_uhf_group.lean:22: lemma diagonalEmbed_lt [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/inductive_colimit_uhf_group.lean:26: lemma diagonalEmbed_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/inductive_colimit_uhf_group.lean:35: theorem finite_stage_card [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/inductive_colimit_uhf_group.lean:161: theorem uhf_colimit_dyadic_bridge [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/krein_souriau_full.lean:157: theorem energy_conservation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/primon_system.lean:35: theorem logPrimeEnergy_pow [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/primon_system.lean:66: theorem mellinDirichlet_add [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/primon_system.lean:112: theorem zetaPartition_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/rigorous_proofs.lean:167: theorem sector_J_cpx [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/rigorous_proofs.lean:170: theorem sector_J_mod [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/rigorous_proofs.lean:173: theorem sector_nullProjector [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/rigorous_proofs.lean:195: theorem sector_ellipticExpChart [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/rigorous_proofs.lean:259: theorem KMS_statement [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/test_braid.lean:61: lemma yang_baxter_id [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/uhf_cantor_boundary.lean:19: lemma diagonalEmbed_lt [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/uhf_cantor_boundary.lean:23: lemma diagonalEmbed_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/uhf_ladder.lean:67: theorem detSign_clE [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/uhf_ladder.lean:70: theorem detSign_clF [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/zeta_zeros_moebius_klein.lean:38: theorem zetaInvolution_involutive [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/zeta_zeros_moebius_klein.lean:42: theorem zetaInvolution_re [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Auto/zeta_zeros_moebius_klein.lean:73: theorem zeta_zero_potential_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Automath/SpectralSquashCayleyDKT.lean:48: theorem cayley_denom_ne [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/CentralChargeCalc.lean:176: lemma zMonomialF_zero_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/CentralChargeCalc.lean:180: lemma zMonomialF_one_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/CentralChargeCalc.lean:184: lemma zMonomialF_two_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/CentralChargeCalc.lean:188: lemma zMonomialF_three_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/CentralChargeCalc.lean:192: lemma zMonomialF_four_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/CentralChargeCalc.lean:196: lemma zMonomialF_five_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/CentralExtension.lean:122: lemma bracket_smul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/Commutator.lean:34: lemma commutator_comm [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/Commutator.lean:38: lemma mul_eq_mul_add_commutator [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/Commutator.lean:113: lemma algebraCommutator'_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/CyclicTripleSum.lean:72: lemma cyclicTripleSum_map_add_fst_of_map_add [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/CyclicTripleSum.lean:79: lemma cyclicTripleSum_map_add_snd_of_map_add [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/CyclicTripleSum.lean:86: lemma cyclicTripleSum_map_smul_fst_of_map_smul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/CyclicTripleSum.lean:130: lemma cyclicTripleSum_map_smul_of_bilin [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/FockSpace.lean:161: lemma heisenbergTri_kgen_mem_cartan [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/FockSpace.lean:165: lemma heisenbergTri_jgen_zero_mem_cartan [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/HeisenbergAlgebra.lean:224: lemma add_def' [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/HeisenbergAlgebra.lean:253: lemma kgen_eq_ofCentral_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/HeisenbergAlgebra.lean:255: lemma kgen_eq' [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/LieAlgebraModuleUEA.lean:71: lemma Algebra.scalar_smul_eq_smul_algebraMap_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/LieAlgebraModuleUEA.lean:85: lemma moduleScalarOfModule.smul_def [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/LieAlgebraModuleUEA.lean:254: lemma UniversalEnvelopingAlgebra.mkAlgHom_surjective [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/LieCohomologySmallDegree.lean:174: lemma apply_add [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/LieCohomologySmallDegree.lean:176: lemma apply_add [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/LieCohomologySmallDegree.lean:178: lemma apply_smul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/LieCohomologySmallDegree.lean:180: lemma apply_smul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/LieCohomologySmallDegree.lean:261: lemma add_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/LieCohomologySmallDegree.lean:264: lemma smul_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/LieVerma.lean:194: lemma VermaHW.upper_smul_hwVec [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/Sugawara.lean:274: lemma sugawaraGen_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/ToMathlib/Algebra/Lie/Basic.lean:17: lemma LieAlgebra.bracketHom_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/ToMathlib/Topology/Algebra/BigOperators/FinProd.lean:5: lemma Finset.sum_eq_sum_support [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/VermaModule.lean:82: lemma one_cyclic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/VirasoroAlgebra.lean:96: lemma add_def' [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/VirasoroAlgebra.lean:125: lemma cgen_eq_ofCentral_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/VirasoroAlgebra.lean:127: lemma cgen_eq' [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/VirasoroCocycle.lean:52: lemma virasoroCocycleBilin_apply_lgen_lgen [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/VirasoroVerma.lean:150: lemma virasoroTri_cgen_mem_cartan [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/VirasoroVerma.lean:154: lemma virasoroTri_lgen_zero_mem_cartan [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/WittAlgebra.lean:75: lemma bracket_lgen_lgen' [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/External/Virasoro/WittAlgebra.lean:88: lemma bracket_antisymm [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Fenchel.lean:25: lemma bregmanDiv_three_point [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Fibonacci/FibAnyonThm1.lean:13: lemma h5sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Fibonacci/FibAnyonThm2.lean:13: lemma h5sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Fibonacci/FibAnyonThm2.lean:33: lemma sqrt_ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Fibonacci/HexagonCocycle.lean:46: theorem hexagon_as_cocycle [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Foundations/NewtonKantorovichSequence.lean:82: theorem majorantSeq_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Foundations/NewtonKantorovichSequence.lean:193: theorem majorantSeq_two_formula [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/BilingualPoincareMetric.lean:76: theorem sub [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/BilingualPoincareMetric.lean:161: theorem imaginaryQuadratic_eq_kHeightQuadratic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/BilingualPoincareMetric.lean:411: theorem zero_op [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/BilingualPoincareMetric.lean:428: theorem add_op [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/BilingualPoincareMetric.lean:445: theorem neg_op [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/BilingualPoincareMetric.lean:462: theorem sub_op [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/BilingualPoincareMetric.lean:524: theorem moebiusTangentPushForward_op [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/BilingualPoincareMetric.lean:746: theorem commutator_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/BilingualUpperHalfPlane.lean:177: theorem denominator_phase_linear_comp [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/BilingualUpperHalfPlane.lean:333: theorem moebiusMap_tau [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/ConstructiveCauchyKernel.lean:60: theorem scalar_resolvent_identity_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/ConstructiveCauchyKernel.lean:74: theorem scalarVerifiedInverse_left_inv [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/ConstructiveKasparov.lean:170: theorem kernelIndex_eq_even_count_sub_odd_count [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/ConstructiveKasparov.lean:180: theorem kernelIndex_eq_zero_of_kernelBasis_eq_nil [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/ConstructiveKasparov.lean:249: theorem defect_eq_one_sub_square [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/ConstructiveKasparov.lean:264: theorem Pker_eq_defect_readout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/ConstructiveKasparov.lean:295: theorem index_eq_projected_kernel_index [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/DualFlat.lean:69: lemma eGeodesic_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/DualFlat.lean:143: lemma mGeodesic_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/DualFlat.lean:150: lemma dualCoord_mGeodesic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/DualFlat.lean:437: lemma projectiveDivergence_eq_kl [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/EntanglementGeometry.lean:408: theorem left_exterior_to_right_interior [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/EntanglementGeometry.lean:417: theorem right_exterior_to_left_interior [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/EntanglementGeometry.lean:531: theorem bell_alice_bob [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/EntanglementGeometry.lean:538: theorem bell_bob_alice [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/EntanglementGeometry.lean:562: theorem measurement_creates_global_knot [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/EntanglementGeometry.lean:621: theorem complexity_nil [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/EntanglementGeometry.lean:628: theorem complexity_append_gate [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/EntanglementGeometry.lean:637: theorem complexity_append [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/EntanglementGeometry.lean:694: theorem bridgeLength_grow [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/EntanglementGeometry.lean:743: theorem zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/EntanglementGeometry.lean:750: theorem succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/EntanglementGeometry.lean:826: theorem circuitAt_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/EntanglementGeometry.lean:927: theorem quantumRecurrenceScale_eq_two_pow_quantumMaxComplexityScale [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/ErlangerPhaseGeometry.lean:143: theorem sub [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/FiniteDefectStokesModel.lean:82: theorem P_apply_one_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/FiniteDefectStokesModel.lean:171: theorem geometricDerivative_ccForm_eq_defect [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/FiniteDefectStokesModel.lean:177: theorem boundaryIntegral_ccForm [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/FiniteDefectStokesModel.lean:182: theorem volumeIntegral_defect [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/FiniteMatrixResolventKernel.lean:134: theorem matrixResolventKernelOfUnit_kernel [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/FiniteMatrixResolventKernel.lean:203: theorem scalarOneByOneResolventKernel_entry [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/GromovHyperbolicity.lean:53: lemma gromovProductAt_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/MobiusClassification.lean:70: theorem classifySigma_loxodromic_of_second_ne_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/MobiusClassification.lean:93: theorem classifySigma_parabolic_of_eq_four [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/MobiusDual2x2.lean:43: theorem hyperbolic_fixed_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/MobiusDual2x2.lean:79: theorem hyperbolic_forward_multiplier_repelling [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/MobiusInfinitesimal.lean:63: theorem parabolic_vectorField [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/MobiusInfinitesimal.lean:67: theorem hyperbolic_vectorField [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/MobiusInfinitesimal.lean:71: theorem elliptic_vectorField [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/OrbitCurrentStokes.lean:155: theorem finiteDefect_isClosedOrbit [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/ParavectorZornBoundary.lean:75: theorem isZornNull_boundary_iff_isNull [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/PhaseErlanger.lean:132: theorem sub [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/RealMoebiusAction.lean:74: theorem moebius_y [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/RealMoebiusAction.lean:84: theorem moebius_y_pos [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/RealMoebiusAction.lean:171: theorem smul_def [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/RealMoebiusAction.lean:174: theorem one_smul_real [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/RealRotorCore.lean:151: theorem realModularDenominatorNormSq_eq_realMoebiusDenSq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/RealUpperHalfPlane.lean:50: theorem ellipticI_x_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/RealUpperHalfPlane.lean:69: theorem ellipticRhoLeft_y_pos [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/RealUpperHalfPlane.lean:73: theorem ellipticRhoLeft_x_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/RealUpperHalfPlane.lean:92: theorem ellipticRhoRight_y_pos [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/RealUpperHalfPlane.lean:96: theorem ellipticRhoRight_x_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/RealUpperHalfPlane.lean:108: theorem ellipticRho_y_pos [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/RealUpperHalfPlane.lean:112: theorem ellipticRho_x_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/SpectralDivisors.lean:444: theorem phasePeriod_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Geometry/SpectralDivisors.lean:675: theorem enclosedMultiplicity_eq_sum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/GrandUnification/CelikErlangenBraidBridge.lean:55: theorem sigma1_squared [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/GrandUnification/CelikErlangenBraidBridge.lean:60: theorem sigma2_squared [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/GrandUnification/CelikErlangenBraidBridge.lean:65: theorem yang_baxter_braid_relation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/GrandUnification/HodgeTrifactorBridge.lean:98: theorem hodgeSectorProjector_exact [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/GrandUnification/HodgeTrifactorBridge.lean:101: theorem hodgeSectorProjector_coexact [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/GrandUnification/HodgeTrifactorBridge.lean:104: theorem hodgeSectorProjector_harmonic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/GrandUnification/HodgeTrifactorBridge.lean:123: theorem hodgeSectorComponent_exact [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/GrandUnification/HodgeTrifactorBridge.lean:126: theorem hodgeSectorComponent_coexact [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/GrandUnification/HodgeTrifactorBridge.lean:129: theorem hodgeSectorComponent_harmonic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/GrandUnification/HodgeTrifactorBridge.lean:144: theorem T_annihilates_harmonicSector [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/GrandUnification/HodgeTrifactorBridge.lean:149: theorem T_on_exactSector [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/GrandUnification/HodgeTrifactorBridge.lean:154: theorem T_on_coexactSector [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/GrandUnification/HodgeTrifactorBridge.lean:179: theorem linearMap_map_harmonicSector [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/GrandUnification/HodgeTrifactorBridge.lean:185: theorem linearMap_map_exactSector [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/GrandUnification/HodgeTrifactorBridge.lean:191: theorem linearMap_map_coexactSector [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/GrandUnification/Su2Su3ProjectiveBridge.lean:20: lemma sum_fin_3 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/GromovWittenErlangen/CP1DrazinModel.lean:144: theorem edgeDrazinData_element_line [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/GromovWittenErlangen/CP1DrazinNilpotentCountRayExample.lean:234: theorem edgeDrazinData_element_line [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/GromovWittenErlangen/CP1DrazinNilpotentCountRayExample.lean:239: theorem edgeLocalizedDrazinResidue_line [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/GromovWittenErlangen/CP1DrazinNilpotentDefectModel.lean:103: theorem edgeDrazinData_element_line [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/GromovWittenErlangen/CP1DrazinNilpotentDefectModel.lean:108: theorem edgeLocalizedDrazinResidue_line [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/GromovWittenErlangen/Examples/DIIITopologicalCountExample.lean:75: theorem counts_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/GromovWittenErlangen/Examples/DIIITopologicalCountExample.lean:80: theorem counts_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/GromovWittenErlangen/ProjectiveCountBridge.lean:92: theorem normalizedShape_scale_counts_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/GroupTheory/AutomorphismTower.lean:54: theorem towerCard_stable [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Hestenes/SpacetimeAlgebra.lean:123: theorem dirac_operator_iff_residual_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Information/BergmanBregman.lean:12: theorem bergmanLocalization_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Jordan/LogDet.lean:73: lemma logdet_square_nonneg_of_posDef [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Jordan/SPD.lean:21: lemma SPD.transpose_eq_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/JordanNormalForm.lean:38: lemma JordanBlock_diag [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/JordanNormalForm.lean:48: lemma JordanBlock_else [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/KK/CompactOperatorBridge.lean:15: lemma isCompactEnd_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/KK/CompactOperatorBridge.lean:19: lemma isCompactEnd_add [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/KK/CompactOperatorBridge.lean:24: lemma isCompactEnd_smul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/KK/RealSplitKreinResolvent.lean:61: lemma isCompactOperator [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/KTheory/Dadarlat.lean:64: theorem gammaMap_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Krein/Cl55Certificates.lean:22: theorem pseudoscalar_sq_cert [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Krein/Cl55Certificates.lean:25: theorem affineNullRoot_sq_cert [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Krein/Cl55Certificates.lean:28: theorem centralExtension_sq_cert [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Krein/Cl55Certificates.lean:31: theorem isometry_error_cert [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Krein/Cl55Certificates.lean:34: theorem operator_det_cert [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Krein/FundamentalSymmetryProjectors.lean:77: theorem K_minus_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Krein/HilbertBridge.lean:267: lemma fst_coe [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Krein/HilbertBridge.lean:268: lemma snd_coe [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Krein/HilbertBridge.lean:269: lemma fst_val [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Krein/KreinSpace.lean:107: lemma kreinInner_symm [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Krein/KreinSpace.lean:110: lemma kreinInner_add_left [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Krein/KreinSpace.lean:114: lemma kreinInner_add_right [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Krein/KreinSpace.lean:118: lemma kreinInner_smul_left [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Krein/KreinSpace.lean:393: lemma signFlipMap_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Krein/PolarizedSector.lean:104: theorem spectralProj_decomposition [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Krein/SplitBoost.lean:88: theorem splitBoost_preserves_norm [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Krein/SplitComplex.lean:45: theorem krein_split_sign_has_nonzero_zero_divisors [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Krein/SplitComplex.lean:50: theorem one_add_eps_mul_one_sub_eps_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/KreinCarrierInstances_tmp.lean:93: theorem modularGeneratorKlein_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/KreinCarrierInstances_tmp.lean:148: theorem concreteRotorFlowKlein_rotor_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/KreinCarrierInstances_tmp.lean:151: theorem concreteRotorFlowKlein_rotorInv_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/KreinCarrierInstances_tmp.lean:223: theorem concreteCoreProjectorKlein_core_krein_selfadjoint [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/KreinCarrierInstances_tmp.lean:264: theorem concreteRelativeFredholmKlein_relativePartitionReadout_eq_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/KreinCarrierInstances_tmp.lean:302: theorem concreteBridgeKlein_kreinTrace [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/LLM/MirrorPhaseCrystalBridge.lean:72: theorem crystalChildAttentionWeight_eq_twoBranchAttentionWeight [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/LLM/MirrorPhaseCuntzAttention.lean:67: theorem twoBranchAttentionWeight_sum_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/LLM/MirrorPhaseCuntzAttention.lean:117: theorem mirrorAttentionMatrix_row_sum_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/LLM/MirrorPhaseCuntzAttention.lean:143: theorem mirrorAttention_kills_branchAnomaly [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/LLM/SinkhornDefectFlow.lean:640: theorem dissipatedHeatRN_nonneg [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/LanglandsGWBridge.lean:138: theorem constructSymplecticWeylVolumeData_quotient [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/LanglandsGWBridge.lean:275: theorem splitBoundaryMetricBracket_eq_zero_of_boundary_dual_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Lie/Pin55KreinConformalBridge.lean:250: theorem exists_pin55_krein_conformal_package [proof_hole]
  - contains `sorry`/`admit`

lean/InfoGeometry/Lie/RealSplitOctonionDerivationWitness.lean:106: theorem rot01Real_up0_readout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Lie/RealSplitOctonionG2Classification.lean:144: theorem derivation_rank_nullity [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Lie/RealSplitOctonionG2Classification.lean:158: theorem finite_g2two_boundary_order [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Lie/RealSplitOctonionG2Classification.lean:171: theorem current_status_is_exactComputerAlgebraLieAlgebra [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Lie/SagerschnigS2S3Distribution.lean:66: theorem sagerschnigDistribution_formula [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Lie/SagerschnigS2S3Distribution.lean:75: theorem sagerschnigDistribution_first_tangent_constraint [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Lie/SagerschnigS2S3Distribution.lean:82: theorem sagerschnigDistribution_beta_formula [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Lie/SplitOctonion235Distribution.lean:50: theorem splitOctonion235Packet_dimensions [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Lie/SplitOctonion235Distribution.lean:62: theorem splitOctonion235TraceIncidence_formula [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Lie/SplitOctonionNonmultiplicativity.lean:46: theorem ex_prod_imaginary [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Lint/NonTriviality.lean:204: def isNontrivialExternalConst [proof_hole]
  - contains `sorry`/`admit`

lean/InfoGeometry/Lint/NonTriviality.lean:404: def auditTransitiveDependencies [proof_hole]
  - contains `sorry`/`admit`

lean/InfoGeometry/Lint/Pauli.lean:48: def pauliLinter [proof_hole]
  - contains `sorry`/`admit`

lean/InfoGeometry/MaxEnt/JaynesInfoStatMech.lean:406: lemma modularConj_diag_entry [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Measure/Projective.lean:22: lemma AEAddConst.refl [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Meta/BridgeTarget.lean:35: def checkBridgeTargets [proof_hole]
  - contains `sorry`/`admit`

lean/InfoGeometry/Meta/EssenceOfInductiveProof.lean:122: theorem propagate_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Meta/EssenceOfInductiveProof.lean:199: theorem recursiveTrajectory_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Meta/InductionHandbook.lean:233: theorem map_id_demo [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Meta/InductionHandbook.lean:256: theorem succ_positive_suffices [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Meta/InductionHandbook.lean:929: theorem wfAccessibleNat [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Meta/OwnerTarget.lean:67: def checkOwnerTargets [proof_hole]
  - contains `sorry`/`admit`

lean/InfoGeometry/Meta/StrictDef.lean:16: def forbiddenTermKinds [proof_hole]
  - contains `sorry`/`admit`

lean/InfoGeometry/Meta/Trust.lean:86: def collectHardEvidence [proof_hole]
  - contains `sorry`/`admit`

lean/InfoGeometry/Modular/PSL2Z.lean:82: theorem val_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Modular/PSL2Z.lean:180: theorem mul_mk [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Monster/MonsterMoonshineThermal.lean:56: theorem monster_order_factorization [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/AlbertCubicTripotent.lean:40: theorem cubicResidual_specializes_to_tripotent_residual [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/AndreevBoundary.lean:431: theorem diagonal_fixed_of_boundary_witness [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/AnomalyTubuleStability.lean:55: theorem anomaly_eq_readout_variation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/CARFermionParity.lean:29: lemma s_add [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/CARFermionParity.lean:30: lemma s_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/CARFermionParity.lean:31: lemma s_central [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ChiralPackingEnergy.lean:263: theorem reorient_chirality [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ChiralPackingEnergy.lean:270: theorem sameRay_reorient [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ChiralPackingEnergy.lean:279: theorem isBenign_reorient [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ChiralPackingEnergy.lean:305: theorem supportCard_reorientAll [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/CliffordAtomsZ2n.lean:214: theorem flipCharge_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/CliffordAtomsZ2n.lean:220: theorem flipCharge_of_ne [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/CliffordAtomsZ2n.lean:263: theorem sectorSign_flip_of_ne [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/CliffordCARFockParity.lean:39: theorem n0_fermionNumber [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ClosureInvolution.lean:431: theorem antiProjection_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ClosureInvolution.lean:497: theorem fixedProjection_theta [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ClosureInvolution.lean:503: theorem antiProjection_theta [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/Basic.lean:44: theorem apply_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/Basic.lean:58: theorem id_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/Basic.lean:112: theorem smul_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/CharPoly.lean:80: theorem charPoly_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/CharPoly.lean:117: theorem eigenvalue_root_charPoly [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/ComplexVectorSpaces.lean:48: theorem neg_one_smul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/ComplexVectorSpaces.lean:81: theorem mem_complex_span_singleton_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/DerivationBound.lean:36: theorem single [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/DerivationBound.lean:101: theorem transSteps_single [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/ExtraGeneral.lean:78: theorem complex_star_mul_self_eq_normSq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/ExtraJordanNormalForm.lean:27: theorem matrix_entry_explicit [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/ExtraJordanNormalForm.lean:75: theorem list_map_add_vec [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/FiniteMatrix.lean:41: theorem ketPi_apply_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/FiniteMatrix.lean:45: theorem ketPi_apply_of_ne [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/FiniteMatrix.lean:55: theorem matrixOp_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/FiniteMatrix.lean:103: theorem matrixOp_conjTranspose_apply_ket [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/Functionals.lean:37: theorem norm_innerRight [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/GNSConcrete.lean:44: lemma pi_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/GNSConcrete.lean:49: lemma gns_vector_state_recovers_state [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/GNSFinite.lean:53: theorem omegaVec_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/GNSFinite.lean:57: theorem vector_state_recovers_omega [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/GNSFiniteSupport.lean:67: theorem liftMul_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/GNSFiniteSupportOperator.lean:34: theorem liftLinear_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/GNSFiniteSupportOperator.lean:43: theorem liftOp_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/GNSFiniteSupportQuotientAlgebra.lean:22: theorem sameGNS_refl [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/GNSFiniteSupportStatePositivity.lean:23: theorem positive_square_term_eq_norm_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/GNSFiniteTwoPoint.lean:50: theorem omegaVec_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/GNSFiniteTwoPoint.lean:53: theorem omegaVec_apply_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/GNSFiniteTwoPoint.lean:56: theorem omegaVec_apply_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/GNSFiniteTwoPoint.lean:60: theorem vector_state_recovers_omega [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/GramSchmidt.lean:129: theorem adjuster_cons [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/InnerProduct.lean:40: theorem cinner_smul_left [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/InnerProduct.lean:44: theorem cinner_smul_right [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/InnerProduct.lean:48: theorem cinner_diff_left [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/InnerProduct.lean:52: theorem cinner_diff_right [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/InnerProduct.lean:71: theorem cinner_smul_real_left [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/InnerProduct.lean:75: theorem cinner_smul_real_right [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/Ket.lean:51: theorem ket_apply_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/OrthogonalProjection.lean:85: theorem projectionToSubmodule_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/OrthogonalProjection.lean:89: theorem projection_mem [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/OrthogonalProjection.lean:93: theorem projection_eq_self_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/OrthogonalProjection.lean:98: theorem projection_minimal [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/OrthogonalProjection.lean:102: theorem projection_range [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/OrthogonalProjection.lean:106: theorem projection_ker [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/OrthogonalProjection.lean:110: theorem projection_idempotent [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/OrthogonalProjection.lean:114: theorem projection_norm_le [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/RieszAdjoint.lean:56: theorem cadjoint_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/RieszAdjoint.lean:84: theorem norm_cadjoint [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/RieszAdjoint.lean:88: theorem cadjoint_eq_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/RieszAdjoint.lean:92: theorem star_eq_cadjoint [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/RieszAdjoint.lean:96: theorem isSelfAdjoint_iff_cadjoint_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/RieszAdjoint.lean:100: theorem isSelfAdjoint.cadjoint_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/RieszRepresentation.lean:80: theorem integralPositiveLinearMap_realRieszMeasure [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/RingHomMatrix.lean:76: theorem toRingHom_apply_toReal [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/RingHomMatrix.lean:125: theorem matReal_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/ScalarMultiplication.lean:55: theorem leftMul_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/ScalarMultiplication.lean:68: theorem rightMul_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/SchurDecomposition.lean:94: theorem diagList_length [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/SchurDecomposition.lean:546: theorem tailMatrix_eq_submatrix [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/SchurDecomposition.lean:551: theorem tailMatrix_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/VSConnect.lean:88: theorem cols_length [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ConformalCrossover.lean:113: theorem sameRay_refl [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ConformalCrossover.lean:200: theorem crossover_generator [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ConstructiveCasimir.lean:67: theorem assocCommutator_zero_right [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ConstructiveCayley.lean:51: theorem self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ConstructiveCayley.lean:83: theorem sub [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ContinuumLimit.lean:47: theorem continuumParabolicFlow_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ContinuumLimit.lean:137: theorem projection_fixes_flow [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/DrazinRepresentedSplit.lean:243: theorem defect_nil_supported [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/DrazinRepresentedSplit.lean:250: theorem core_supported [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/DualSplitOctonion.lean:90: theorem coordinate_count [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/DualSplitOctonion.lean:121: theorem primal_projection_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/DualSplitOctonion.lean:130: theorem lifted_associator_base [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/DualSplitOctonion.lean:178: theorem id_fixes_epsilon [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/DualSplitOctonionAlgebra.lean:159: theorem dual_coordinate_count [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/DualSplitOctonionAlgebra.lean:223: theorem primal_projection_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/DualSplitOctonionAlgebra.lean:231: theorem lifted_associator_base [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/DualSplitOctonionAlgebra.lean:248: theorem zero_dual_defect_klein_bottle_z2_invariant [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/DualSplitOctonionAlgebra.lean:253: theorem zero_dual_defect_klein_boundary_charge_even [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/DualSplitOctonionRootKleinBraidBridge.lean:47: theorem square_root_grade_one_lands_even [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/DualSplitQuaternionBackbone.lean:82: theorem i_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/DualSplitQuaternionBackbone.lean:85: theorem j_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/DualSplitQuaternionBackbone.lean:88: theorem k_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/DualSplitQuaternionBackbone.lean:91: theorem ij_eq_k [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/DualSplitQuaternionBackbone.lean:94: theorem ji_eq_neg_k [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/DualSplitQuaternionBackbone.lean:97: theorem jk_eq_neg_i [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/DualSplitQuaternionBackbone.lean:100: theorem kj_eq_i [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/DualSplitQuaternionBackbone.lean:103: theorem ki_eq_j [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/DualSplitQuaternionBackbone.lean:106: theorem ik_eq_neg_j [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/DualSplitQuaternionBackbone.lean:109: theorem ijk_eq_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/DualSplitQuaternionBackbone.lean:161: theorem coordinate_count [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/DualSplitQuaternionBackbone.lean:200: theorem primal_projection_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ErlangenJaynesGromov.lean:86: theorem act_mul_alg [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ErlangenJaynesGromov.lean:202: theorem pullbackFunctional_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ErlangenJaynesGromov.lean:823: theorem dualEpsilon_sq_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/FibonacciCantorCuntzBoundary.lean:62: theorem fibonacciAdjacency_entries [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/FibonacciCantorCuntzBoundary.lean:70: theorem fibonacciPathCount_recursion [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/FibonacciCantorCuntzBoundary.lean:76: theorem fibonacciPathCount_initial [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/FiniteJonesOptics.lean:118: theorem det2_diagJones [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/FresnelJonesReflection.lean:230: theorem circularReflection_brewster_apply_left [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/G22CartanFiniteLaws.lean:44: theorem boost_so55_skew [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/G2TwoAutomorphismTheorem.lean:100: theorem outerC2Witness_fixed_point_count [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/G2TwoAutomorphismTheorem.lean:104: theorem outerC2Witness_transposition_count [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/G2TwoAutomorphismTheorem.lean:108: theorem outerC2Witness_degree [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/G2TwoHexagonIncidenceWitness.lean:60: theorem point_count_eq_line_count [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/G2TwoHexagonIncidenceWitness.lean:79: theorem unique_candidate_line_orbit_count [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/G2TwoHexagonIncidenceWitness.lean:83: theorem outer_witness_fixed_point_count [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/G2TwoHexagonIncidenceWitness.lean:87: theorem all_fixed_point_line_count_eq_three [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/G2TwoHexagonIncidenceWitness.lean:91: theorem setwise_fixed_line_count_eq_nine [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/IndividuatedCayley.lean:47: theorem self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/JUnitaryTopologicalCharge.lean:375: theorem topologicalCharge_eq_one_of_det_eq_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/JUnitaryTopologicalCharge.lean:383: theorem topologicalCharge_eq_neg_one_of_det_eq_neg_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/JaynesFiniteState.lean:76: theorem finiteEmpiricalFunctional_map_smul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/JaynesFiniteState.lean:109: theorem finiteEmpiricalState_map_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/JonesCalibration.lean:183: theorem jones_apply_offdiag_one_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/KasparovKreinDIIIBridge.lean:30: theorem finite_andreev_reflection_eq_neg_time_reversal [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/KasparovKreinDIIIBridge.lean:35: theorem finite_diii_time_reversal_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/KasparovKreinDIIIBridge.lean:62: theorem finite_andreev_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/KasparovKreinDIIIBridge.lean:67: theorem finite_andreev_compat_with_topological_closure [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/KasparovKreinDIIIBridge.lean:115: theorem concrete_topological_socket_matches_diii_time [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/KleinBerryConnectionFinite.lean:57: theorem monodromyDerivativeCorrection_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/KleinBerryConnectionFinite.lean:62: theorem transformConnection_Ax [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/KleinBerryConnectionFinite.lean:67: theorem transformConnection_Ay [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/KleinBerryConnectionFinite.lean:81: theorem phaseParity_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/KleinBerryConnectionFinite.lean:96: theorem antisymmetric_boundary_klein_invariant_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/KleinBerryConnectionFinite.lean:101: theorem zero_path_klein_boundary_even [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/KreinIsotropicCone.lean:260: theorem null_nil_supported [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ModularSignCPT.lean:77: theorem Kmod_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ModularSignCPT.lean:211: theorem Kmod_square_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ModularSignCPT.lean:216: theorem complexStructure_square [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ModularSignCPT.lean:326: theorem Kmod_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ModularSignCPT.lean:514: theorem Kmod_square_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ModularSignCPT.lean:519: theorem partialComplexStructure_square [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/NoncommutativeBogoliubovKANLift.lean:102: theorem connesCocycle_same_weight [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/NoncommutativeBogoliubovKANLift.lean:147: theorem typeIII_baseIntegral_eq_modularWeight_integral [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/NoncommutativeBogoliubovKANLift.lean:157: theorem typeIII_coreTraceOfBase_eq_coreTrace_traceOfEmbedded [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/NoncommutativeBogoliubovKANLift.lean:341: theorem diagonal_shadow_available [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/OperatorChiralLightcone.lean:50: theorem opposite_right [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/OperatorThermodynamics.lean:729: theorem toKMSState_eval [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/OperatorialJonesCalculus/PolarizationProjectors.lean:146: theorem brewsterReflector_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ProjectiveCenterQuotient.lean:54: theorem concreteCenter_involution [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/ProjectiveCenterQuotient.lean:72: theorem id_commutes [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SpectralGeneratorProxy.lean:63: theorem self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SpectralGeneratorProxy.lean:95: theorem sub [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionCuntzInductionBridge.lean:59: theorem UHF_transition_selfadjoint_projection_formula [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionCuntzInductionBridge.lean:68: theorem peirceCuntzTransition_eq_projection_formula [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionCuntzInductionBridge.lean:90: theorem peirce_projection_partition [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionCuntzInductionBridge.lean:118: theorem peirceCuntzTransition_oneZ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionCuntzInductionBridge.lean:122: theorem peirceCuntzTransition_ePlus [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionCuntzInductionBridge.lean:126: theorem peirceCuntzTransition_eMinus [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionCuntzInductionBridge.lean:130: theorem peirceCuntzTransition_H [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionDerivationWitness.lean:54: theorem rot01_kills_diagonal_unit [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionDerivationWitness.lean:58: theorem rot01_nonzero_on_up0 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean:159: theorem leftRegular_normZ_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean:345: theorem ePlus_idempotent [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean:346: theorem eMinus_idempotent [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean:347: theorem ePlus_mul_eMinus [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean:348: theorem eMinus_mul_ePlus [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean:377: theorem up0_mul_up1 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean:378: theorem up1_mul_up2 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean:379: theorem up2_mul_up0 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean:380: theorem up1_mul_up0 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean:381: theorem up2_mul_up1 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean:382: theorem up0_mul_up2 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean:384: theorem down0_mul_down1 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean:385: theorem down1_mul_down2 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean:386: theorem down2_mul_down0 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean:387: theorem down1_mul_down0 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean:388: theorem down2_mul_down1 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean:389: theorem down0_mul_down2 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean:392: theorem associator_up0_up1_down1 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean:395: theorem associator_up0_up1_down1_ne_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean:432: theorem detZ_ePlus [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean:433: theorem detZ_eMinus [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean:494: theorem trZ_mulZ_leak_formula [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean:514: theorem trace_closed_on_pureBosonicSection [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean:531: theorem global_base_conservation_on_pureBosonicSection [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean:663: theorem rawCapacityConnection_readback [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean:678: theorem rawTwiceAlgebraicKLJet_expansion [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean:687: theorem rawDefectCharge_pentagon [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean:691: theorem rawDefectCharge_heptagon [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean:728: theorem conjZ_ePlus [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean:729: theorem conjZ_eMinus [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionMultiplication.lean:730: theorem conjZ_zeroZ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionSymplecticFoundation.lean:63: theorem doubleJordan_up0_down0_up0_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionSymplecticFoundation.lean:69: theorem doubleJordan_up0_down0_up1_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionSymplecticFoundation.lean:75: theorem doubleJordan_up1_down1_up2_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionSymplecticFoundation.lean:90: theorem jacobiator_up0_up1_down0 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionSymplecticFoundation.lean:105: theorem ePlus_add_eMinus_eq_oneZ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionSymplecticFoundation.lean:108: theorem H_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionSymplecticFoundation.lean:111: theorem detZ_H [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionSymplecticFoundation.lean:114: theorem detZ_oneZ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SplitOctonionSymplecticFoundation.lean:167: theorem J_sq_neg_oneZ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SuperTKKConformalClosure.lean:114: theorem recompose_coordinates [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SuperTKKConformalClosure.lean:120: theorem coordinates_recompose [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SuperVirasoroExtension.lean:211: theorem virasoroProject_central_commutes [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SuperVirasoroExtension.lean:225: theorem virasoroProject_lgen_bracket [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SymmetryInvariants.lean:105: theorem act_mul_op [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SymmetryInvariants.lean:183: theorem sub [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SymmetryInvariants.lean:269: theorem one_isProjector [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SymmetryInvariants.lean:273: theorem zero_isProjector [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SymmetryInvariants.lean:758: theorem act_map_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/SymmetryInvariants.lean:894: theorem commutator_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/TomitaCartanSplit.lean:67: theorem map_sub [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/TomitaCartanSplit.lean:952: theorem diagonal_isotropic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/TomitaCartanSplit.lean:1075: theorem diagonal_isotropic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/TomitaCartanSplit.lean:1161: theorem globalGenerator_compact [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OperatorAlgebra/VirasoroProjectPin.lean:113: theorem virasoroIntegration_is_certified [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Optics/FiniteJonesBrewsterCollapse.lean:47: theorem brewsterMatrix_trace [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Optics/FiniteJonesKasparovBoundary.lean:68: theorem kasparovDefect_eq_one_sub_square [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Optics/FiniteJonesKasparovBoundary.lean:158: theorem kernelBasis_eq_modesOf_kasparovDefect [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Optics/FiniteJonesModel.lean:68: theorem diagJones_10 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Optics/FiniteJonesModel.lean:120: theorem det2_diagJones [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Optics/FiniteJonesModel.lean:126: theorem det2_brewsterMatrix [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Optics/FiniteJonesStinespringConstructive.lean:188: theorem toStinespringIsometry_V [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Optics/FiniteJonesStinespringConstructive.lean:208: theorem visibleDefect_eq_environmentGain [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Optics/FiniteJonesStinespringConstructive.lean:295: theorem julia_visible_visible_block [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Optics/FiniteJonesStinespringConstructive.lean:305: theorem julia_hidden_visible_block [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Optics/FiniteJonesStinespringConstructive.lean:315: theorem julia_visible_hidden_block [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Optics/JonesCalculus.lean:104: theorem stokes_horizontal [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Optics/JonesCalculus.lean:107: theorem stokes_vertical [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Optics/JonesCalculus.lean:136: theorem light_follows_null_geodesics [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Optics/JonesCalculusSpinorLorentz.lean:66: theorem birefringent_index_split [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Optics/JonesCalibration.lean:295: theorem secondCoeff_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Optics/OperatorialJonesCalculus.lean:162: theorem brewsterReflector_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OptimalTransport/EntropyGradientFlow.lean:85: theorem bregmanProxStep_eq_jkoEntropyStep [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OptimalTransport/LogDetBarrier.lean:67: theorem componentN_det_ne_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OptimalTransport/LogDetBarrier.lean:78: theorem logAbsDetBarrier2_componentN_eq_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OptimalTransport/LogDetBarrier.lean:87: theorem logDetBurgFromIdentity2_componentN_eq_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/OptimalTransport/LogDetBarrier.lean:108: theorem logAbsDetBarrier2_componentNCongruence [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Optimization/RelativeEntropyObjective.lean:27: theorem relative_entropy_self_eq_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Parafermion/PrimeParafermionGrandCanonicalClock.lean:33: theorem localParafermionFactor_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Parafermion/PrimeParafermionGrandCanonicalClock.lean:37: theorem localParafermionFactor_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Parafermion/PrimeParafermionGrandCanonicalClock.lean:65: theorem stateProbability_three [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/AmplituhedronVolume.lean:44: theorem amplituhedronVolume_eq_zeta_sum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/BogoliubovPauliSolderedFrame.lean:73: theorem bogoliubov_frame_reconstructs_pauli_tetrad_soldering [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/BogoliubovPauliSolderedFrame.lean:110: theorem bogoliubov_frame_eq_pauli_tetrad_soldered_frame [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/BogoliubovSU3ParafermionProofChain.lean:69: theorem qBraid4_comp [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/BogoliubovSU3ParafermionProofChain.lean:97: theorem bdgMajoranaPlusColorSpinor4_color_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/BogoliubovSU3ParafermionProofChain.lean:103: theorem bdgMajoranaPlusColorSpinor4_singlet_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/BogoliubovSU3ParafermionWeld.lean:110: theorem bdgParafermionPlus4_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/BostConnesGNS.lean:38: theorem kmsState_critical [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/BostConnesThermalTime.lean:118: theorem modularFlowCl11_e1_coord [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/BostConnesThermalTime.lean:223: theorem bostConnesDirichletTerm_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/BoundaryMajoranaMassGap.lean:40: theorem majoranaPairSplitting_eq_two_mul_gap [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/BoundaryMajoranaMassGap.lean:86: theorem chiralMajoranaCentralCharge_eq_half_net [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/CStarCuntzTensorQuotient.lean:70: theorem isometry_relation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/CStarCuntzTensorQuotient.lean:75: theorem orthogonal_relation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/ChiralCausalCone.lean:361: theorem trace_eq_two_coeffI [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/ChiralTensorRecoupling.lean:58: theorem e_eq_X_add_Y_add_Z [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/ChiralTensorRecoupling.lean:239: theorem projector_tensor_identity [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/ChiralTensorRecoupling.lean:430: theorem loop_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/ColorCARStandardModel.lean:176: theorem N_plus_add_N_minus [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/ColorCARStandardModel.lean:181: theorem N_plus_sub_N_minus [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/ColorCARStandardModel.lean:186: theorem N_plus_mul_N_minus [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/ColorCARStandardModel.lean:190: theorem N_minus_mul_N_plus [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/CuntzDeformedSuperPoincare.lean:165: theorem poincareComp_actMomentum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/FermionicAndreevReflection.lean:45: theorem andreevReflection_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/FineStructureDerivation.lean:60: theorem alpha_value [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/FineStructureModels.lean:43: theorem alpha_p_def [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/FisherKreinLorentz.lean:67: theorem modularTimeCovector4_of_ne_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/FreeEntropyCalibrationVariationPacket.lean:79: theorem S_free_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/FreeEntropyCalibrationVariationPacket.lean:91: theorem S_freeFirstVariation_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/FreeEntropyCalibrationVariationPacket.lean:110: theorem effectiveStressReadout_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/FreeEntropyDiffusionFunctional.lean:32: theorem freeEntropyFirstVariation_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/FreeEntropyDiffusionFunctional.lean:53: theorem majoranaFreeEntropyEnergy_sixteen [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/FreeEntropyDiffusionFunctional.lean:75: theorem reverseFreeDrift_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/FreeEntropyDiffusionFunctional.lean:110: theorem totalVariation_stationary_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/FreeEntropySouriauBridge.lean:36: theorem S_free_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/FreeEntropySouriauBridge.lean:63: theorem cartanSFree_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/FreeEntropySouriauBridge.lean:102: theorem S_freeFirstVariation_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/FreeEntropySouriauBridge.lean:125: theorem cartanSFreeFirstVariation_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/FreeEntropySouriauBridge.lean:159: theorem effectiveStressTensorReadout_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/GellMannParafermionSolder.lean:44: theorem gellMannParafermionSolder_color_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/GellMannParafermionSolder.lean:51: theorem gellMannParafermionSolder_singlet_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/HestenesCuntzPhaseSpace.lean:92: theorem stageCoordinate_compatible [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/HestenesCuntzPhaseSpace.lean:96: theorem stageMomentum_compatible [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/HestenesCuntzPhaseSpace.lean:211: theorem constantTwoCellWeylFamily_phase [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/HestenesCuntzSpacetimeAlgebra.lean:61: theorem coordinate_duals_recover [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/KMSFisherBridge.lean:28: theorem modularHamiltonian_of_det_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/KMSFisherBridge.lean:36: theorem fisherWeight_of_det_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/KreinBornRule.lean:65: theorem modifiedBornProbability_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/KreinBornRule.lean:73: theorem modifiedBornProbability_one_nonneg [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/LorentzBoostMinkowski.lean:49: theorem boostX_preserves_minkowskiSq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/LorentzChiralCuntzBridge.lean:76: theorem chiralConjAct_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/LorentzChiralCuntzBridge.lean:81: theorem chiralConjAct_add [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/LorentzChiralCuntzBridge.lean:98: theorem det_chiralConjAct [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/LorentzChiralCuntzBridge.lean:256: theorem sl2cSpinTransport_eq_chiralConjAct [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MD006OperatorEigenoperators.lean:48: theorem leftMul_comp [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MD006OperatorEigenoperators.lean:53: theorem rightMul_comp [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MD006OperatorEigenoperators.lean:58: theorem leftMul_rightMul_commute [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MD008RepresentationCharge.lean:130: theorem matrix_unit_weight_charges [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MD010GaugeSSB.lean:139: theorem diagVEV_trace_square [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MD010GaugeSSB.lean:148: theorem diagFluctuation_trace_square [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MD012EmergentModelsFinite.lean:102: theorem lorentzSignMetric4_time_entry [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MD012EmergentModelsFinite.lean:107: theorem lorentzSignMetric4_space1_entry [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MD014TriSpinZ3Projectors.lean:178: theorem trace3_sectorPhase [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MD014TriSpinZ3Projectors.lean:223: theorem finiteCentralExtensionMul_fst [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MD014TriSpinZ3Projectors.lean:229: theorem finiteCentralExtension_kernel_add [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MD015QuantumCorrectionsFinite.lean:58: theorem effectiveActionThreeLoop_eq_twoLoop_add_cubic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MD015QuantumCorrectionsFinite.lean:65: theorem effectiveActionThreeLoop_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MD015QuantumCorrectionsFinite.lean:87: theorem oneLoopTraceLogShadow_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MD015QuantumCorrectionsFinite.lean:95: theorem quadraticFluctuationAction_sub_background_of_stationary [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MD015QuantumCorrectionsFinite.lean:101: theorem quadraticFluctuationAction_even_of_stationary [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MD015QuantumCorrectionsFinite.lean:117: theorem frgScalarRHS_zero_cutoffDerivative [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MD016ExperimentalPredictionsFinite.lean:42: theorem crossSectionFactor_zero_alpha [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MD016ExperimentalPredictionsFinite.lean:47: theorem crossSectionFactor_zero_energy [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MD016ExperimentalPredictionsFinite.lean:64: theorem linearTrialityAngleShift_zero_delta [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MD016ExperimentalPredictionsFinite.lean:79: theorem gwSpeedShadow_zero_frequency [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MD016ExperimentalPredictionsFinite.lean:100: theorem gwBetaCoeff_zero_gamma [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MD20250430070955FinitePartition.lean:97: theorem finiteCovariance_zero_left_of_constant [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MD20250430071017MatrixStatistics.lean:90: theorem covarianceCoeff_zero_of_constant [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MDPASJMSouriau.lean:70: theorem wedge_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MDPASJMSouriau.lean:79: theorem wedge_self_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MDPASJMSouriauCantorColimit.lean:95: theorem turingTapeReadout_eq_cantorLimitMap [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MDPASJMSouriauCantorColimit.lean:159: theorem mdpas_witt_bits_eq_cantor_prefix [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MDPASJMSouriauCantorColimit.lean:190: theorem cantorPrefixProjection_ofStage [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MDPASJMSouriauCantorColimit.lean:198: theorem turingWindow_readout_ofStage [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MDPASJMSouriauDigest.lean:542: theorem compatibleLift_ofStage [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MDPASJMSouriauDigest.lean:584: theorem bond_entropy_production [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/MDPASJMSouriauGlobalObstruction.lean:47: theorem sphereArea_closed [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/OrbitClassification55.lean:88: theorem determinant_self_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/ParabolicClock.lean:35: theorem parabolic_trace_two [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/PellisfineStructure.lean:67: theorem pellis_alpha_inv_v9_readback [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/Pin55Explicit.lean:27: lemma sum_fin_2 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/Section29QuantumEffectiveAction.lean:39: theorem effectiveActionTwoLoop_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/Section29QuantumEffectiveAction.lean:71: theorem runningCoupling_eq_initial_of_zero_slope [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/Section29QuantumEffectiveAction.lean:97: theorem condensateResidual_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/Section31UnifiedMatrixDynamics.lean:53: theorem curvatureConst_zero_left [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/Section31UnifiedMatrixDynamics.lean:58: theorem covDerivConst_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/Section31UnifiedMatrixDynamics.lean:82: theorem covDerivConst_conjugation_covariant [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/Section33PauliBiquaternionCompletion.lean:66: theorem pauliCoeff0_eq_trace_div_two [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/Section34StrengthenedFormalism.lean:46: theorem covariantDensityDerivative_zero_connection [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/Section34StrengthenedFormalism.lean:51: theorem covariantDensityDerivative_zero_partial [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/Section36ConformalCoordinateAlgebra.lean:78: theorem blochResidual_axis [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/Section36ConformalCoordinateAlgebra.lean:112: theorem hamiltonianAsymmetry_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/Section38StressEnergyDomainSeparation.lean:73: theorem fullStress_eq_compact_of_zero_connectionVariation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/SouriauMassieuPlanckFunctional.lean:143: theorem souriauFreeEntropyAction_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/SplitCliffordAlgebras.lean:169: theorem ePos_eNeg_jordan_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/SplitCliffordAlgebras.lean:503: theorem OP_charpoly_factor [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/SplitOctonionBraidSU3.lean:145: theorem nullVector_norm_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/SupergradedCuntzBdG.lean:352: theorem RindlerWeylFlow_add [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/SupergradedCuntzBdG.lean:389: theorem cuntzBdGAffineEnsemble_zero_rapidity_bracket [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/SupergradedCuntzBdG.lean:435: theorem complexStarCuntzBdGAffineEnsemble_zero_rapidity_bracket [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/SupergradedCuntzBdG.lean:441: theorem complexStarCuntzBdGAffineEnsemble_logScale_bracket [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/SupergradedCuntzBdG.lean:456: theorem StarAlgHom.map_affineSuperBracket [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/SupergradedCuntzBdG.lean:465: theorem StarAlgHom.map_qAffineSuperBracket [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/SupergradedCuntzBdG.lean:474: theorem StarAlgHom.map_grandCanonicalBracket [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/SupergradedCuntzBdG.lean:696: theorem star_bdgMajoranaPlus [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/SupergradedCuntzBdG.lean:702: theorem bdgMajoranaPlus_sq_eq_hamiltonianAtom [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/SupergradedCuntzBdG.lean:728: theorem grandCanonicalWeightedBracket_even_left [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/SupergradedCuntzBdG.lean:735: theorem grandCanonicalWeightedBracket_even_right [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/TKKZorn.lean:81: theorem TKKFisherInformationMetric_eq_detZ_polar [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/Universe1000333SpinTorsionScale.lean:50: theorem spinDensityMagnitude_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/WeylSU3ColorSymmetry.lean:125: theorem weylAct_smul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/ZornBraidScalingCovariance.lean:64: theorem leftRegularMatrix_Q_k [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/ZornBraidScalingCovariance.lean:69: theorem leftRegularMatrix_R_k [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/ZornBraidScalingCovariance.lean:169: theorem scaledZornPhi_conjugate [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/ZornMatrixSU3/ZornSU3Properties.lean:138: theorem zorn_left_alternative [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/ZornMatrixSU3/ZornSU3Properties.lean:143: theorem zorn_right_alternative [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/ZornNuclearState.lean:33: lemma det_vacuum_1 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/ZornNuclearState.lean:34: lemma det_vacuum_2 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/ZornNuclearState.lean:36: lemma det_quark [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/ZornNuclearState.lean:39: lemma det_antiquark [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/ZornNuclearState.lean:46: lemma sum_ite_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/ZornTkkAlgebraicClosure.lean:33: theorem commutator_jacobi [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/ZornTkkAlgebraicClosure.lean:40: theorem lieBracket_eq_commutator [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Physics/ZornTkkOrchestration.lean:32: theorem defectSheetTransition_preserves_splitPair [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Prequantum/GNSBridge.lean:62: theorem state_quadratic_nonneg [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Prequantum/GNSBridge.lean:69: theorem algebraic_cauchy_schwarz [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Prequantum/LiouvilleCapacity.lean:112: theorem symplectic_preservation_eq_det_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Prequantum/Scaling.lean:57: theorem PrequantumData.rescaleHbar_curvature [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Prequantum/Scaling.lean:61: theorem PrequantumData.rescaleHbar_hbar [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Probability/HomologicalProbability.lean:281: theorem regularTreePercolationThreshold_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/FactorStratifiedDeRhamCertificate.lean:129: theorem observedAudit_pairCodim [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/FactorStratifiedDeRhamCertificate.lean:133: theorem observedAudit_tripleCodim [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/FactorStratifiedDeRhamCertificate.lean:137: theorem observedAudit_singularLocusCodim [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/FactorStratifiedDeRhamCertificate.lean:141: theorem observedAudit_factorStrings [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/FactorStratifiedDeRhamCertificate.lean:148: theorem observedAudit_not_closed [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/FactorStratifiedDeRhamCertificate.lean:152: theorem observedAudit_fullProduct_timeout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/FactorStratifiedDeRhamCertificate.lean:156: theorem observedAudit_degreeZero_timeout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/FactorStratifiedDeRhamCertificate.lean:160: theorem observedAudit_fullDeRham_timeout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/FactorStratifiedDeRhamCertificate.lean:164: theorem observedAudit_dlocalizeExt_timeout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/FiveGradedCentralizer.lean:182: theorem mobiusClosureFromConformalInversion2_gw_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/FiveGradedTopologicalBridge.lean:55: theorem spin_socket_ribbon_twist_eq_minus_id [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/FiveGradedTopologicalInvariants.lean:83: theorem spinStructureUnobstructed_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/KleinQuadricGrothendieckDeRham.lean:68: theorem grothendieckLog_deriv_log [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/KleinQuadricGrothendieckDeRham.lean:73: theorem grothendieckLog_deriv_neg_log [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/KleinQuadricGrothendieckDeRham.lean:89: theorem grothendieckWinding_of_sheet [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/KleinQuadricMonodromy.lean:65: theorem holonomyPhase_is_root_of_unity [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/KleinQuadricMonodromy.lean:93: theorem logDerivative_at [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/KleinQuadricMonodromy.lean:98: theorem negLogDerivative_at [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/KleinQuadricTime.lean:142: theorem tripotent_square_idempotent [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/KleinQuadricTime.lean:250: theorem timeCohomology_exp_eq_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/KuzminCuntzPath.lean:93: theorem seed_toeplitz_limit [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/MacaulayTrackBIngestion.lean:101: theorem arithmeticVolumeF3_status [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/MacaulayTrackBIngestion.lean:106: theorem arithmeticVolumeF3_not_external_verified [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/MacaulayTrackBIngestion.lean:125: theorem candidateBettiRank_status [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/MacaulayTrackBIngestion.lean:130: theorem candidateBettiRank_not_external_verified [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/ModularMonodromyClock.lean:76: theorem nullConeFlow_trace [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/NonIsoConf3RankIngestion.lean:80: theorem candidateLocalBettiData_consistent [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/NonIsoConf3RankIngestion.lean:85: theorem candidateLocalBettiData_totalRank [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/Null.lean:81: lemma IsGradePlusRay_vacuum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/Null.lean:84: lemma IsGradeMinusRay_vacuum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/PenroseDAGAmplituhedronRosetta.lean:72: theorem laneEquiv_sameInCommon [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/ProjectiveMap.lean:21: lemma map_smul_gauge [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/ProjectiveMap.lean:52: lemma projectiveMap_mk [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/ProjectiveMap.lean:58: lemma projectiveMap_vacuum [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/ProjectiveMap.lean:63: lemma projectiveMap_mk_gauge [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/ProjectiveMap.lean:76: lemma projectiveMapEven_mk [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/ProjectiveMap.lean:112: lemma modular_j_gauge_equivariant [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/ProjectiveMap.lean:117: lemma spectral_epsilon_gauge_equivariant [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/ProjectiveMap.lean:122: lemma complex_i_gauge_equivariant [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/Quadrics/Polarization.lean:43: theorem add_left [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/Quadrics/Polarization.lean:49: theorem add_right [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/Quadrics/Polarization.lean:55: theorem smul_left [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/Quadrics/Polarization.lean:60: theorem smul_right [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/Quadrics/Polarization.lean:116: theorem poincareMetricLinear_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/Quadrics/SignatureDeterminant.lean:44: theorem det_ellipsoidQuadric [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/Quadrics/SignatureDeterminant.lean:48: theorem det_hyperboloidQuadric [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/Quadrics/SignatureDeterminant.lean:52: theorem det_paraboloidQuadric [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/QuaternionicKreinForm.lean:26: theorem splitOctonionKreinQuadratic_formula [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/RohozhkinDelaunayScramblingBridge.lean:46: theorem rohozhkinTriangleBasisDim_eq_two_mul_add_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/SplitOctonions/OctonionicProjectiveLine.lean:90: theorem lemma452ResidualB_eq_zero_of_left_v21_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/SplitOctonions/OctonionicProjectiveLine.lean:96: theorem lemma452ResidualB_eq_zero_of_right_v21_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/SplitOctonions/Polar.lean:224: theorem projectivePolarIncidence_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/SplitOctonions/Polar.lean:234: theorem nullRayMk_eq_scaleNull [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/SplitOctonions/Polar.lean:244: theorem incident_mk_scale_both_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/SplitOctonions/SplitOctonionsColorStabilizer.lean:88: theorem longitudinal_invariant [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/SplitOctonions/ThreeDimensionalRealization.lean:49: theorem dot3Bilin_symm [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/SplitOctonions/VoelkelSectionPacket.lean:41: theorem norm_eq_halfPairing [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/SplitOctonions/ZornBaseProjection.lean:37: theorem baseProjection_eq_flowRelativeVolumeRN [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/SplitOctonions/ZornBaseProjection.lean:44: theorem baseProjection_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/SplitOctonions/ZornBaseProjection.lean:52: theorem baseProjection_comp [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/SplitOctonions/ZornConcrete.lean:278: theorem concretePolarDatum_polarZ_eq_polarExpr [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/SplitOctonions/ZornFlowRelativeVolume.lean:36: theorem flowRelativeVolumeRN_eq_zornRelativeVolumeRN [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/SplitOctonions/ZornFlowRelativeVolume.lean:64: theorem flowRelativeVolumeRN_id [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/TwistorSpace.lean:52: theorem twistorNorm_smul_right [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/TwistorSpace.lean:56: theorem twistorNorm_smul_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/TwistorSpace.lean:76: theorem projective_twistor_classification_disjoint [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Projective/TwistorSpace.lean:82: theorem projective_twistor_sign_trichotomy [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/AttentionBridge.lean:23: theorem split_softmax_weight_formula [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/CuntzPrimonRestPoincare.lean:37: theorem restPauliParavector_minkowskiNormSq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/FiniteEntanglementComplexityCore.lean:162: theorem copyBobToCharlie_b_eq_c [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/FiniteEntanglementComplexityCore.lean:194: theorem hammingWeight_simpleString [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/FiniteEntanglementComplexityCore.lean:247: theorem classicalSingleFlipComplexity_simple [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/FiniteEntanglementComplexityCore.lean:308: theorem cost_singleton [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/FiniteEntanglementComplexityCore.lean:316: theorem cost_append_gate [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/FiniteEntanglementComplexityCore.lean:325: theorem cost_append [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/GeometricTensorTest.lean:25: theorem ofMajorana_g_eq_metric [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/KitaevChain.lean:61: theorem macroscopicVolume_eq_prod_pfaffians [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/KitaevChain.lean:68: theorem macroscopicVolume_append [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/KitaevChain.lean:130: theorem hasDefect_singleton_iff_isCritical [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/ModularAnomaly.lean:65: lemma sigma_zero_clm [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/PoincareSupercharge.lean:29: theorem casimir_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/Qutrit.lean:42: theorem qutritRegisterIndex_card [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/Qutrit.lean:47: theorem qutritRegisterSpace_finrank [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/Qutrit.lean:86: theorem state_normalization_three [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/QutritBraidIncidenceBridge.lean:121: theorem qutritGeneralizedPauliX_eq_shift [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/QutritBraidIncidenceBridge.lean:126: theorem qutritGeneralizedPauliZ_eq_sectorPhase [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/QutritGates.lean:124: theorem rotationHamiltonian_coe [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/QutritMobiusTripotentOrientationBridge.lean:181: theorem qutritMobiusMatrixFlow_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/QutritProjectiveColorBridge.lean:49: theorem qutritCarrier_finrank [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/QutritProjectiveColorBridge.lean:54: theorem colorSingletCarrier_finrank [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/RealKCategory.lean:232: lemma roundTrip_smul_eq_smulRoundTrip [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/RealMajorana.lean:390: lemma transportJ_apply_B [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/RealMajorana.lean:394: lemma Binv_apply_transportJ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/SouriauFoliationFiniteShadow.lean:66: theorem rotationalEngine_add [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/SouriauFoliationFiniteShadow.lean:76: theorem modularConjugation_reflects_modularHamiltonian [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/SouriauFoliationFiniteShadow.lean:82: theorem tomitaOperator_eq_product [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/SplitCliffordAtom.lean:64: lemma Hom.comm_j [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/SplitCliffordAtom.lean:68: lemma Hom.comm_eps [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/StateSpace.lean:95: theorem parabolicRNDensity_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/StateSpace.lean:100: theorem parabolicRNDensity_sub_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/ThermofieldDouble.lean:62: theorem tfdCoeff_zero_time [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quantum/ThermofieldDouble.lean:79: theorem tfdCoeffSupported_eq_zero_of_not_mem [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quiver/KoroteevZeitlinMirror.lean:283: theorem HilbK_dim [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quiver/KoroteevZeitlinMirror.lean:423: theorem instantonModuli_dim [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quiver/KoroteevZeitlinMirror.lean:429: theorem instantonModuli_dim_sym [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Quiver/TKKHamiltonian.lean:111: theorem isospinWeight [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Renyi.lean:52: lemma RenyiD_eq_log_Phi_shift_div [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Section12.lean:80: theorem torsionTensor_eq_two_lowerAntisymmetrization [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Section12.lean:87: theorem torsionTensor_antisymmetric_lower [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Section12.lean:93: theorem torsionTensor_repeated_lower [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Section12.lean:99: theorem torsionTensor_zero_of_lower_symmetric [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Section12.lean:133: theorem torsionTensor_flat [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Section12.lean:172: theorem torsionTwoFormCoeff_flat [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Section12.lean:205: theorem contorsionFromTorsion_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Section12.lean:239: theorem spinConnectionWithContorsion_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Section12.lean:245: theorem spinConnectionWithContorsion_flat [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Section12Formalized.lean:71: theorem torsionTensor_zero_of_lower_symmetric [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Section12Formalized.lean:212: theorem quaternionConnection_real_eq_dot [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Section13.lean:239: theorem gammaExpectation_zero_state [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Section20.lean:43: theorem torsion_coefficient_definitions_agree [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Section20.lean:68: theorem quaternion_torsion_definitions_agree [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Section20.lean:77: theorem finite_shift_commutator_is_generic_readout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Section24.lean:43: theorem derivativeCommutatorCoeff_antisymmetric [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Section26.lean:69: theorem electromagneticFieldShadow_antisymmetric [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Section26.lean:76: theorem electromagneticFieldShadow_diagonal_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Section7.lean:54: theorem soldering_diagonal [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Section7.lean:79: theorem Gamma_symmetric [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Section7.lean:85: theorem spin_connection_vanishes_flat [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Section8.lean:220: theorem quaternionConnection_real [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Section8.lean:270: theorem spinConnectionFlat_antisymmetric [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Section8.lean:274: theorem tetrad_postulate_flat [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Section9.lean:126: theorem riemannCurvature_flat [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Section9.lean:168: theorem quaternion_spin_riemann_flat_chain [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Singular/DrazinGreen.lean:37: theorem A_mul_Drazin_Green_eq_projector [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Singular/DrazinGreen.lean:137: theorem A_mul_drazinGreen_eq_drazinProjector [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Singular/SchurDrazinMoorePenrose.lean:26: theorem drazinRegular_add_residue [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Spectral/Algebra/SpectralSequence.lean:52: theorem toPage_d [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Spectral/Cohomology/Sandbox.lean:51: lemma differential_shift_is_shiftK [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Spectral/Colimit/Basic.lean:88: theorem comp_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Spectral/Colimit/Basic.lean:111: theorem SplitCliffordSystem_step [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Spectral/Colimit/Basic.lean:148: theorem SplitCliffordInclusion_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Spectral/Homotopy/EM.lean:31: theorem EM_base [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Spectral/Homotopy/EM.lean:45: theorem EMRing_step [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Spectral/Homotopy/EM.lean:58: theorem SplitCliffordHomotopyGroup_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Spectral/Homotopy/Smash.lean:34: theorem SmashProduct_map_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Spectral/Homotopy/Smash.lean:70: theorem SplitCliffordSmash_base [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Spectral/Homotopy/Suspension.lean:113: theorem LoopSpace_map_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Spectral/Homotopy/Suspension.lean:151: theorem IteratedLoopSpace_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Spectral/Homotopy/Wedge.lean:50: theorem WedgeSum.carrierComm_base [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Spectral/Spectrum/Basic.lean:69: theorem SplitCliffordPrespectrum_step [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Spectral/Spectrum/Basic.lean:79: theorem bottClockStage_sub_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Spectral/Spectrum/Basic.lean:83: theorem bottClockStage_pos [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/SuperMetriplectic/Axioms.lean:92: theorem netOddShadow_eq_right_minus_left [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/SuperMetriplectic/Axioms.lean:204: theorem effectiveEvenOnsager_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/SuperMetriplectic/Axioms.lean:214: theorem drazinDefectProjector_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/SuperMetriplectic/Cl44WeylD4.lean:76: theorem coordinate_i [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/SuperMetriplectic/Cl44WeylD4.lean:137: theorem cartan_rank_four [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/SuperMetriplectic/SouriauTomitaBKM.lean:457: theorem solverReady_of_chebyshev [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Tensor/DeBruijn.lean:154: theorem ofPorts_portCompatible_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Tensor/DeBruijn.lean:213: theorem lift_portCompatible [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Tensor/DeBruijnFin.lean:103: theorem ofFinPorts_portCompatible_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Tensor/DeBruijnFin.lean:188: theorem ofFinPorts_portCompatible_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Tensor/DeBruijnLift.lean:68: theorem lift_inScope [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Tensor/DeBruijnLift.lean:86: theorem lift_shiftSound [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Tensor/DeBruijnPorts.lean:95: theorem ofPorts_portCompatible_iff [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Tensor/DeBruijnPorts.lean:138: theorem lift_ofPorts [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Tessellation/CantorDiracSeaWalk.lean:106: theorem boundaryPrefix_one_false [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Tessellation/NilpotentFlow.lean:24: theorem oneAddSquareZeroUnit_val [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Tessellation/NilpotentFlow.lean:30: theorem oneAddSquareZeroUnit_inv_val [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Tessellation/NilpotentFlow.lean:137: theorem IncidentLightray.flowUnit_val [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Tessellation/VolumeTransport.lean:66: theorem squareZeroUnit_inv_val [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Tessellation/VolumeTransport.lean:115: theorem lightrayFlowUnit_inv_val [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Tessellation/VolumeTransport.lean:148: theorem incidentLightrayFlowUnit_inv_val [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Tessellation/WilsonLoop.lean:40: theorem WilsonLoop.defect_eq_zero_iff_flat [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Thermal/FiniteMatrix.lean:99: lemma partition_pos [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Thermal/FiniteMatrix.lean:105: lemma gibbsWeight_pos [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Thermal/FiniteMatrix.lean:113: lemma gibbsWeight_sum_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Thermal/FiniteMatrix.lean:194: lemma internalEnergy_eq_gibbsExpectation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Thermal/FiniteMatrix.lean:219: lemma thermalState_modularShift_invariant [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Thermo/AmariSouriauBridge.lean:72: theorem logPotential_bregman_eq_legendre_bregman [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Thermo/FiniteDiagonal.lean:144: lemma modularShift_diag_fixed [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Thermo/FiniteDiagonal.lean:198: lemma gibbsDensity_diag_pos [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Thermo/FiniteDiagonal.lean:203: lemma gibbsDensity_diag_le_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Thermo/Gibbs.lean:95: lemma softMin_def [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Thermo/KMSDetailedBalance.lean:57: theorem standardKMSRegion_upperBoundary [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Thermo/SusceptibilityHessian.lean:136: theorem susceptibility_eq_hessian_response [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Thermo/SusceptibilityHessian.lean:144: theorem susceptibility_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Thermo/SusceptibilityHessian.lean:162: theorem toSusceptibilityDatum_susceptibility [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Thermo/SusceptibilityHessian.lean:255: theorem toDielectricResponseDatum_epsilon [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Thermodynamics/FiniteConnesCocycle.lean:123: theorem finitePositiveDensityRatioAtTime_hasDerivAt_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Thermodynamics/FiniteConnesCocycle.lean:158: theorem finiteCommutingConnesPhase_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Thermodynamics/FiniteGibbsRelative.lean:176: theorem finiteScalarRelativeCocycle_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Thermodynamics/ProjectiveTemperature.lean:45: theorem betaInvert_involutive [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Thermodynamics/ProjectiveTemperature.lean:50: theorem betaInvert_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Thermodynamics/ProjectiveTemperature.lean:67: theorem one_lt_betaInvert_of_mem_Ioo_zero_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Thermodynamics/ProjectiveTemperature.lean:84: theorem one_isFixed_temperatureClosure [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Thermodynamics/SouriauModularS.lean:56: theorem modularSLiftInversion_element [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Thermodynamics/SouriauTemperatureProjective.lean:246: theorem smul_eq_self_of_stationary [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Thermodynamics/SouriauTemperatureProjective.lean:254: theorem read_lift [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Thermodynamics/SouriauTemperatureProjective.lean:362: theorem smul_eq_self_of_stationary [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Thermodynamics/SouriauTemperatureProjective.lean:370: theorem read_lift [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Thermodynamics/SouriauTemperatureProjective.lean:436: theorem closure_theta [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topological/FibonacciAnyons.lean:82: theorem B_matrix_eq_FRF [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topological/FibonacciCasimir.lean:34: theorem trace2_R_matrixOf [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topological/FibonacciCasimir.lean:39: theorem trace2_F_matrixOf [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/AharonovBohmConcreteVortex.lean:21: theorem omega_isPrimitiveRoot [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/AmplituhedronBoundaryRank32.lean:88: theorem boundaryRank32State_card [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/AnyonicBraidedVolume.lean:62: theorem evalBraidWord_cons [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/ArtinBraidS3Quotient.lean:32: theorem s3ArtinGenerator_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/ArtinBraidS3Quotient.lean:37: theorem s3ArtinGenerator_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/ArtinBraidS3Quotient.lean:63: theorem s3ArtinGenerator_braid_relation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/ArtinCentralizerMonodromy.lean:38: theorem negI_sq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/ArtinCentralizerMonodromy.lean:57: theorem centralFromWinding_even [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/ArtinCentralizerMonodromy.lean:72: theorem adjacent_artin_monodromy [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/ArtinCentralizerMonodromy.lean:78: theorem separated_artin_monodromy [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/ArtinCentralizerMonodromy.lean:97: theorem odd_unit_winding_negI [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/ArtinCentralizerMonodromy.lean:101: theorem even_unit_winding_I [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/ArtinMonodromyPin55.lean:80: theorem o55_preserves_split_form [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/BraidNegativeIdentityMonodromy.lean:40: theorem spinor_adjacent_artin [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/BraidNegativeIdentityMonodromy.lean:45: theorem B2_full_twist_negative [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/BregmanDivergence.lean:12: theorem topologicalBregmanDiv_self [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/BrillouinKleinBerryConnectionFinite.lean:66: theorem transformAx_zero_derivative [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/BrillouinKleinBerryConnectionFinite.lean:71: theorem transformAy_zero_derivative [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/BrillouinKleinBerryConnectionFinite.lean:80: theorem klein_z2_orientation_reversal_cancel [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/BrillouinKleinBerryConnectionFinite.lean:85: theorem phaseParity_add_two [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/BrillouinKleinBerryConnectionFinite.lean:90: theorem phaseParity_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/CantorDiracGrandCanonical.lean:172: theorem gibbsWeight_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/CantorDiracOperator.lean:93: theorem finiteCantorDirac_apply [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/CantorDiracOperator.lean:102: theorem finiteCantorDirac_eq_smul_id [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/CliffordMobiusDeRhamMonodromy.lean:49: theorem cl11_mobius_recovers_sl2c [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/CuntzMap.lean:44: theorem map_unital [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/DelaunayPureBraidRepresentation.lean:44: theorem pureBraidMatrixRepresentationOfRelators_of [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/DelaunayPureBraidRepresentation.lean:88: theorem trivialPureBraidRepresentation_of [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/DiscreteDiracHodgeChiral.lean:163: theorem eckmann_degree_one_laplacian_readout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/DiscreteHodgeStabilizer.lean:93: theorem stabilizerHamiltonian1_eq_hodgeLaplacian1 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/EckmannDiscreteHodge.lean:34: lemma eckmannDot_zero_right [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/GeneralizedCircleMobius.lean:44: lemma mobius_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/GeneralizedCircleMobius.lean:47: lemma coeff_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/KANWallpaperSuperchargeReadout.lean:44: theorem glide_self_anticomm_eq_double_translation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/KleinCompatibleWallpaperClassification.lean:189: theorem pg_is_currently_verified [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/KleinCompatibleWallpaperClassification.lean:206: theorem current_verified_class_iff_pg [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/Metriplectic.lean:41: theorem energy_conservation [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/Metriplectic.lean:46: theorem entropy_evolution [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/MobiusCantorTKKClosure.lean:39: theorem mobiusJ_involutive [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/MobiusCantorTKKClosure.lean:44: theorem mobiusGamma_involutive [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/MobiusCantorTKKClosure.lean:49: theorem mobiusJ_gamma_commute [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/MobiusCantorTKKClosure.lean:54: theorem mobiusGammaJ_involutive [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/MobiusCrossRatio.lean:74: lemma delta_matrix [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/MobiusGeometry.lean:894: lemma translation_transform_eval_some [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/MobiusGeometry.lean:899: lemma translation_transform_eval_none [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/MobiusGeometry.lean:977: lemma dilation_transform_eval_some [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/MobiusGeometry.lean:982: lemma dilation_transform_eval_none [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/MobiusGeometry.lean:991: lemma inversion_transform_eval_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/MobiusGeometry.lean:996: lemma inversion_transform_eval_none [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/MobiusGeometry.lean:1149: lemma eval_inv_left [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/MobiusGeometry.lean:2243: theorem loxodromic_trace [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/MobiusGeometry.lean:2245: theorem real_trace_sq_nonneg [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/MobiusRecoveredHelpers.lean:132: lemma eval_inv_left [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/NonorientableExceptionalKleinGlide.lean:49: theorem dx_glide [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/PapadakisPrimes.lean:151: theorem goldbachPairingRecover_readout [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/PapadakisPrimes.lean:170: theorem primeDiscriminantEndpoint_of_prime [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/ParafermionIdentityRealization.lean:32: theorem idRealization_spinor_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/ParafermionIdentityRealization.lean:38: theorem gellMannSolder_idRealization [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/PenroseBraidLorentzFinite.lean:34: theorem pentagridReflect_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/Pin55ReflectionGlide.lean:50: theorem reflect0_preserves_splitNorm [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/PointedGroups.lean:52: theorem conjugatingBraidAction_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/PointedGroups.lean:57: theorem conjugatingBraidAction_mul [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/Q8V4SchurBridge.lean:51: theorem q8ToV4_central_two [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/RohozhkinRepresentation.lean:55: theorem representation_of [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/SpinorOrbitStratum.lean:151: theorem q55NegAll_preserves_q55 [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/SuperCuntzDilationCurvature.lean:143: theorem qDeficit_eq_qWarped_sub_flat [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/SuperCuntzDilationCurvature.lean:149: theorem qDeficit_zero_of_q_one_and_flat_volume [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/ThermodynamicGauge.lean:33: theorem entropy_production_eq_commutator [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/ThermodynamicGauge.lean:48: theorem entropy_production_eq_zero_iff_detailed_balance [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/ThermodynamicGauge.lean:104: theorem nonabelian_wilson_word_nil [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/ThermodynamicGauge.lean:109: theorem finite_wilson_loop_nil [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/ThermodynamicGauge.lean:114: theorem nonabelian_wilson_word_append_singleton [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/ThermodynamicGauge.lean:119: theorem finite_wilson_loop_append_singleton [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/ThermodynamicGauge.lean:124: theorem nonabelian_wilson_word_singleton [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/ThermodynamicGauge.lean:129: theorem finite_wilson_loop_singleton [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/ThermodynamicSL2MobiusFlow.lean:52: theorem thermodynamicSL2Generator_matrix [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/ThermodynamicSL2MobiusFlow.lean:65: theorem thermodynamicSL2VectorField_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/ThermodynamicSL2MobiusFlow.lean:95: theorem thermodynamicSL2MatrixFlow_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/ThermodynamicSL2MobiusFlow.lean:379: theorem hasDerivAt_finiteOrbit_eq_explicit [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/ThermodynamicSL2MobiusFlow.lean:392: theorem finiteOrbitJacobian_eq [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/ThermodynamicSL2MobiusFlow.lean:422: theorem finiteOrbitJacobian_ne_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/ThermodynamicSL2MobiusFlow.lean:625: theorem finiteOrbitJacobian_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/ThermodynamicSL2MobiusFlow.lean:630: theorem logJacobianNorm_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/ThermodynamicSL2MobiusFlow.lean:635: theorem boltzmannLogJacobianEntropy_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/ThreeStackBraidLorentzMetriplectic.lean:59: theorem boost_conj_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/TwistedBoundaryExceptionalPoints.lean:79: theorem typeII_case3_cannot_be_dp [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/V4RootSystem.lean:92: theorem varlamov_v4_inversion [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/V4RootSystem.lean:96: theorem v4_reflections_commute [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/WallpaperRepresentationTable.lean:46: theorem allRows_length [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/WallpaperRepresentations.lean:131: theorem generic_little_group_order_eq_one [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/WallpaperRepresentations.lean:136: theorem generic_irrep_profile_one_dimensional [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/WallpaperRepresentations.lean:141: theorem p4m_gamma_irrep_profile [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/WallpaperRepresentations.lean:146: theorem p6m_gamma_irrep_profile [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/WilsonLoopThermodynamics.lean:66: theorem finite_flow_connection_word_nil [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/WilsonLoopThermodynamics.lean:71: theorem finite_flow_wilson_loop_nil [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/WilsonLoopThermodynamics.lean:76: theorem finite_flow_connection_word_append_singleton [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/WilsonLoopThermodynamics.lean:84: theorem finite_flow_wilson_loop_append_singleton [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/WilsonLoopThermodynamics.lean:91: theorem finite_flow_connection_word_singleton [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Topology/WilsonLoopThermodynamics.lean:96: theorem finite_flow_wilson_loop_singleton [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/TrifactorGeometry.lean:26: theorem det_plus_one_I [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/TrifactorGeometry.lean:27: theorem det_plus_one_symplectic [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/TrifactorGeometry.lean:33: theorem det_zero_null [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/TrifactorGeometry.lean:34: theorem pfaffian_sq_eq_det [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/TrifactorProjectors.lean:55: theorem I_cube_eq_I [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Twistor/PenroseTwistor.lean:40: theorem twistor_space_dim [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Twistor/PenroseTwistor.lean:64: theorem twistorHermitian_smul_right [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Twistor/RollingSpinorMobiusBridge.lean:174: theorem incidenceCoboundary_eq_zero_of_compatible [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Twistor/RollingSpinorMobiusBridge.lean:747: theorem cp1Projection_pullback_incidenceCoboundary [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Volume/DeterminantBundle.lean:50: theorem weylAction_eq_dilation_volumeScale [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Volume/RadonNikodym.lean:42: theorem rn_eq_additiveInvariant [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Volume/RadonNikodym.lean:82: theorem rn_eq_logAbs_vol [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Volume/RadonNikodym.lean:87: theorem rn_eq_additiveInvariant [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Wavelet/PrimeWaveletMRA.lean:20: theorem dyadicScale_zero [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

lean/InfoGeometry/Wavelet/PrimeWaveletMRA.lean:25: theorem dyadicScale_succ [skeletal_proof]
  - proof body appears to be `rfl`/`trivial`/`simp`/`aesop`-only

```

## Notes
- This report is static when lake is unavailable; full proof checking requires successful lake build.
