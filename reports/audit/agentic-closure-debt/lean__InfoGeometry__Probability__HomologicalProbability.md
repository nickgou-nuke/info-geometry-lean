# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:29.762340+00:00`
Root: `lean/InfoGeometry/Probability/HomologicalProbability.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **126**
- Hard: **0**
- Soft: **108**
- Advisory: **18**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Probability/HomologicalProbability.lean` | `advisory` | 234 | 0 | 108 | 18 | 126 |

## Findings by file

### `lean/InfoGeometry/Probability/HomologicalProbability.lean`
- module: `InfoGeometry.Probability.HomologicalProbability`
- status: `advisory`
- debt_score: `234`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L81 [soft] `law-field-locker` in `structure-field CommonInvariantStructure.leftInvariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L82 [soft] `law-field-locker` in `structure-field CommonInvariantStructure.rightInvariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L111 [advisory] `existential-packaging` in `theorem indicator_zeroDivisors_of_disjoint` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L138 [soft] `skeletal-proof` in `theorem hardyWeinbergMap_iterate` — proof appears to close via minimal tactic one-liner
  - L152 [advisory] `local-hypothesis-injection` in `theorem hardyWeinbergMap_iterate` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L257 [soft] `law-field-locker` in `structure-field BBGKYHierarchy.marginal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L259 [soft] `law-field-locker` in `structure-field BBGKYHierarchy.collisionOp` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L279 [soft] `skeletal-proof` in `theorem regularTreePercolationThreshold_eq` — proof appears to close via minimal tactic one-liner
  - L282 [advisory] `existential-packaging` in `def HomologicalPercolationDualityStatement` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L347 [advisory] `existential-packaging` in `def EnergyReachable` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L385 [advisory] `existential-packaging` in `def ScalarFrequencyNotLinguisticInvariant` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L409 [soft] `law-field-locker` in `structure-field WinogradPair.sameSyntax` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L411 [advisory] `existential-packaging` in `theorem syntaxOnlyFailsOnWinogradPair` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L470 [soft] `law-field-locker` in `structure-field SupportInvariantMeasureLike.mono` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L471 [soft] `law-field-locker` in `structure-field SupportInvariantMeasureLike.cup_intersection` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L480 [soft] `law-field-locker` in `structure-field HomologicalProbabilityTheory.assign` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L481 [soft] `law-field-locker` in `structure-field HomologicalProbabilityTheory.mono` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L500 [advisory] `existential-packaging` in `def AlmgrenCycleSpaceStatement` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L556 [advisory] `existential-packaging` in `def GromovWaistStatement` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L699 [soft] `law-field-locker` in `structure-field HomologicalProbabilityPipeline.toConfigSpace` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L700 [soft] `law-field-locker` in `structure-field HomologicalProbabilityPipeline.toFiltration` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L701 [soft] `law-field-locker` in `structure-field HomologicalProbabilityPipeline.toHomInvariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L702 [soft] `law-field-locker` in `structure-field HomologicalProbabilityPipeline.toNumericalShadow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L718 [advisory] `existential-packaging` in `structure ObservableInverse` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L727 [soft] `law-field-locker` in `structure-field ObservableInverse.null_in_kernel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L728 [soft] `law-field-locker` in `structure-field ObservableInverse.observable_disjoint_null` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L729 [soft] `law-field-locker` in `structure-field ObservableInverse.inverse_on_observable` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L740 [soft] `law-field-locker` in `structure-field DrazinRegularizedProbability.projectionToRegular` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L741 [soft] `law-field-locker` in `structure-field DrazinRegularizedProbability.inverseOnRegular` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L742 [soft] `law-field-locker` in `structure-field DrazinRegularizedProbability.invariantOfSingularSector` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L751 [soft] `law-field-locker` in `structure-field StructuredProbability.assign` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L752 [soft] `law-field-locker` in `structure-field StructuredProbability.scalarShadow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L781 [soft] `law-field-locker` in `structure-field IsNoncommutativeProbabilityState.normalized` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L782 [soft] `law-field-locker` in `structure-field IsNoncommutativeProbabilityState.nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L809 [soft] `law-field-locker` in `structure-field GNSData.normalized_vector` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L810 [soft] `law-field-locker` in `structure-field GNSData.reproduces_state` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L884 [soft] `law-field-locker` in `structure-field BooleanLatticeInAlgebra.idempotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L885 [soft] `law-field-locker` in `structure-field BooleanLatticeInAlgebra.orthogonal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L886 [soft] `law-field-locker` in `structure-field BooleanLatticeInAlgebra.partition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L895 [soft] `law-field-locker` in `structure-field SplitCliffordSuperlattice.c` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L896 [soft] `law-field-locker` in `structure-field SplitCliffordSuperlattice.a` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L897 [soft] `law-field-locker` in `structure-field SplitCliffordSuperlattice.numProj` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L898 [soft] `law-field-locker` in `structure-field SplitCliffordSuperlattice.parity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1000 [advisory] `existential-packaging` in `def HasProbabilityDefect` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1053 [soft] `law-field-locker` in `structure-field CliffordProbabilitySystem.c` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1054 [soft] `law-field-locker` in `structure-field CliffordProbabilitySystem.a` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1055 [soft] `law-field-locker` in `structure-field CliffordProbabilitySystem.parity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1056 [soft] `law-field-locker` in `structure-field CliffordProbabilitySystem.jSymmetry` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1057 [soft] `law-field-locker` in `structure-field CliffordProbabilitySystem.state` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1114 [soft] `law-field-locker` in `structure-field FullProbabilityPipeline.toConfigSpace` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1115 [soft] `law-field-locker` in `structure-field FullProbabilityPipeline.toAlgebra` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1116 [soft] `law-field-locker` in `structure-field FullProbabilityPipeline.toInvariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1117 [soft] `law-field-locker` in `structure-field FullProbabilityPipeline.toNumerical` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1160 [advisory] `existential-packaging` in `structure FiveGradedLieAlgebra` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1180 [soft] `law-field-locker` in `structure-field FiveGradedLieAlgebra.gradeSubspace` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1182 [soft] `law-field-locker` in `structure-field FiveGradedLieAlgebra.graded_cover` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1184 [soft] `law-field-locker` in `structure-field FiveGradedLieAlgebra.structureAlgebra_closed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1189 [soft] `law-field-locker` in `structure-field FiveGradedLieAlgebra.graded_bracket` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1215 [soft] `law-field-locker` in `structure-field FiveGradedSymmetryGroup.expMap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1219 [soft] `law-field-locker` in `structure-field FiveGradedSymmetryGroup.struct_mul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1223 [soft] `law-field-locker` in `structure-field FiveGradedSymmetryGroup.exp_lands_in_struct` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1227 [advisory] `existential-packaging` in `structure AffineClosure` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1244 [soft] `law-field-locker` in `structure-field AffineClosure.inclusion` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1246 [soft] `law-field-locker` in `structure-field AffineClosure.extendedAction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1248 [soft] `law-field-locker` in `structure-field AffineClosure.boundary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1250 [soft] `law-field-locker` in `structure-field AffineClosure.decomposition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1254 [soft] `law-field-locker` in `structure-field AffineClosure.action_preserves_open` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1257 [advisory] `existential-packaging` in `def GWBundleIsomorphismStatement` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1348 [advisory] `existential-packaging` in `structure HomogeneousTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1366 [soft] `law-field-locker` in `structure-field HomogeneousTarget.quotientMap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1368 [soft] `law-field-locker` in `structure-field HomogeneousTarget.surjective` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1370 [soft] `law-field-locker` in `structure-field HomogeneousTarget.pInvariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1372 [advisory] `existential-packaging` in `structure LieOrbitCurveWitness` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1390 [soft] `law-field-locker` in `structure-field LieOrbitCurveWitness.orbitDegree` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1392 [soft] `law-field-locker` in `structure-field LieOrbitCurveWitness.coroot_surjective` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1395 [soft] `law-field-locker` in `structure-field LieOrbitCurveWitness.degree_unique` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1416 [soft] `law-field-locker` in `structure-field WeylGraphLocalizationData.weylFixed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1418 [soft] `law-field-locker` in `structure-field WeylGraphLocalizationData.edgeDegree` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1420 [soft] `law-field-locker` in `structure-field WeylGraphLocalizationData.label_injective` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1423 [advisory] `existential-packaging` in `def KleinGromovAlignmentStatement` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1474 [advisory] `existential-packaging` in `def KleinGromovPipelineStatement` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1561 [soft] `law-field-locker` in `structure-field MomentumMapProbabilityPacket.momentumMap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1563 [soft] `law-field-locker` in `structure-field MomentumMapProbabilityPacket.entropyFn` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1599 [soft] `law-field-locker` in `structure-field HomologicalMeasurePacket.observableMap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1601 [soft] `law-field-locker` in `structure-field HomologicalMeasurePacket.supportIdeal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1603 [soft] `law-field-locker` in `structure-field HomologicalMeasurePacket.idealLeq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1605 [soft] `law-field-locker` in `structure-field HomologicalMeasurePacket.idealMul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1607 [soft] `law-field-locker` in `structure-field HomologicalMeasurePacket.mono` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1610 [soft] `law-field-locker` in `structure-field HomologicalMeasurePacket.cup_intersection` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1635 [soft] `law-field-locker` in `structure-field MovingBallConfigurationPacket.inclusionInBase` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1657 [soft] `law-field-locker` in `structure-field CycleVolumeSpectrumPacket.cycleVolume` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1659 [soft] `law-field-locker` in `structure-field CycleVolumeSpectrumPacket.detected` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1661 [soft] `law-field-locker` in `structure-field CycleVolumeSpectrumPacket.spectralVal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1663 [soft] `law-field-locker` in `structure-field CycleVolumeSpectrumPacket.spectralVal_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1698 [soft] `law-field-locker` in `structure-field WeylVolumeGaugePacket.spectrum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1700 [soft] `law-field-locker` in `structure-field WeylVolumeGaugePacket.pWidth` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1882 [soft] `law-field-locker` in `structure-field ClassicalRadonNikodymPacket.rnDensity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1884 [soft] `law-field-locker` in `structure-field ClassicalRadonNikodymPacket.logLikelihood` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1886 [soft] `law-field-locker` in `structure-field ClassicalRadonNikodymPacket.logLikelihood_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1888 [soft] `law-field-locker` in `structure-field ClassicalRadonNikodymPacket.surprisal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1890 [soft] `law-field-locker` in `structure-field ClassicalRadonNikodymPacket.surprisal_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1921 [soft] `law-field-locker` in `structure-field ModularRadonNikodymPacket.modularNCRadonNikodymWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1971 [soft] `law-field-locker` in `structure-field GibbsKMSPacket.freeEnergy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1973 [soft] `law-field-locker` in `structure-field GibbsKMSPacket.relativeEntropyToGibbs` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1975 [soft] `law-field-locker` in `structure-field GibbsKMSPacket.freeEnergyEntropyRelation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1998 [soft] `law-field-locker` in `structure-field GKSLDissipativeDynamicsPacket.lindbladGenerator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L2000 [soft] `law-field-locker` in `structure-field GKSLDissipativeDynamicsPacket.dissipationFunctional` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L2004 [soft] `law-field-locker` in `structure-field GKSLDissipativeDynamicsPacket.entropyDecay` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L2043 [soft] `law-field-locker` in `structure-field ModularThermodynamicBridgePacket.spectralWeightVolumeComparison` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L2225 [soft] `law-field-locker` in `structure-field SpectralVolumeWeightPacket.energyLevel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L2227 [soft] `law-field-locker` in `structure-field SpectralVolumeWeightPacket.spectralVolume` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L2233 [soft] `law-field-locker` in `structure-field SpectralVolumeWeightPacket.boltzmannWeight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L2235 [soft] `law-field-locker` in `structure-field SpectralVolumeWeightPacket.spectralVolume_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L2237 [soft] `law-field-locker` in `structure-field SpectralVolumeWeightPacket.partitionFunction_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L2239 [soft] `law-field-locker` in `structure-field SpectralVolumeWeightPacket.boltzmannWeight_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L2274 [soft] `law-field-locker` in `structure-field SupertraceSupervolumePacket.evenTrace` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L2276 [soft] `law-field-locker` in `structure-field SupertraceSupervolumePacket.oddTrace` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L2278 [soft] `law-field-locker` in `structure-field SupertraceSupervolumePacket.superTrace` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L2280 [soft] `law-field-locker` in `structure-field SupertraceSupervolumePacket.superTrace_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L2374 [soft] `vacuous-prop` in `prop <vacuous>` — Prop declaration appears to reduce to True/False
  - L2524 [soft] `law-field-locker` in `structure-field SpectralThermalNormalizationPacket.beta_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L2526 [soft] `law-field-locker` in `structure-field SpectralThermalNormalizationPacket.energy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L2528 [soft] `law-field-locker` in `structure-field SpectralThermalNormalizationPacket.boltzmannPotential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L2530 [soft] `law-field-locker` in `structure-field SpectralThermalNormalizationPacket.boltzmannPotential_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L2534 [soft] `law-field-locker` in `structure-field SpectralThermalNormalizationPacket.partition_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

