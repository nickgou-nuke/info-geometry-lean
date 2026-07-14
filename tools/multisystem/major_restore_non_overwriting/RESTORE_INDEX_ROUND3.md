# Restore index round 3: non-scratch recovery surfaces

Scope:
- `sandbox/`
- `agent_memory_recovery/`
- `recovery/pre-hermes-snapshot/`
- top-level recovered/test Lean files
- other non-live, non-`.lake`, non-`archive/scratch_recovery` Lean fragments

Inventory artifact:
- `tools/multisystem/major_restore_non_overwriting/non_scratch_recovery_candidates_round3.json`

Policy:
- live owner files remain untouched in this round
- fragments are mapped to current owner context before any recovery file is written
- recovered files are written only under `tools/multisystem/major_restore_non_overwriting/lean/...`
- stale proof sketches are recorded as future isolated lemma tasks, not restored as closure

## 1. Inventory result

The round-3 inventory scanned 929 non-live/non-scratch Lean fragments and ranked the top 250 by imports, declarations, line count, and `sorry` count.

High-ranked families include:
- `ZetaCoordinateSymmetry`
- `ThermodynamicChiralGraphCalculus`
- `HomologicalProbability`
- `SouriauOperatorialLogPotential`
- `SouriauMetriplecticOptimalTransport`
- `O44PinMobiusProjective`
- `KreinDrazinBoundarySupport`
- `MobiusGeometry`

## 2. Classified/restored families

### 2.1 Zeta coordinate symmetry base definitions

Fragments inspected:
- `agent_memory_recovery/ZetaCoordinateSymmetry.lean/2026-07-06_03-46-10_f263f3d1.lean`
- `sandbox/ZetaCoordinateSymmetry.lean`
- live owner context: `lean/InfoGeometry/External/Auto/ZetaCoordinateSymmetry.lean`
- supporting arithmetic owner: `lean/InfoGeometry/Arithmetic/ZetaSouriauComplexLift.lean`

Findings:
- the no-sorry memory snapshot and the live external-auto file have the same 115 declaration names
- the current `sandbox/ZetaCoordinateSymmetry.lean` contains additional front definitions and tail sockets
- the live external-auto file currently fails because four local complex-coordinate names are missing from its namespace:
  - `conjugationReflection`
  - `functionalReflection`
  - `antiunitaryCriticalReflection`
  - `CriticalLine`
- `ZetaSouriauComplexLift.lean` owns related definitions, but importing it alone is not enough: the live proof scripts simplify by unfolding local names in `InfoGeometry.Arithmetic.ZetaCoordinateSymmetry`

Verification:
- `lake env lean lean/InfoGeometry/External/Auto/ZetaCoordinateSymmetry.lean` fails with unknown/function-expected errors at those four names
- `lake env lean sandbox/ZetaCoordinateSymmetry.lean` succeeds, with only four `sorry` warnings in analytic tail sockets
- a temp copy of the live external-auto file with the four local definitions inserted compiles with exit code 0

Recovered file written:
- `tools/multisystem/major_restore_non_overwriting/lean/InfoGeometry/Recovered/ZetaCoordinateSymmetryBaseRecovered.lean`

Recovered declarations:
- `InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.conjugationReflection`
- `InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.functionalReflection`
- `InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.antiunitaryCriticalReflection`
- `InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.CriticalLine`
- small simp readback lemmas for those definitions

Verification of recovered file:
- `lake env lean tools/multisystem/major_restore_non_overwriting/lean/InfoGeometry/Recovered/ZetaCoordinateSymmetryBaseRecovered.lean`
- result: exit code 0, only pre-existing Lake manifest/package warnings

Conclusion:
- this is a genuine depletion recovery, not a duplicate owner
- future live integration should be minimal: move/import this base-definition kernel before the external-auto owner, rather than copying a monolithic sandbox file
- no analytic zeta/RH theorem is introduced

### 2.2 Thermodynamic chiral graph calculus

Fragments inspected:
- `agent_memory_recovery/ThermodynamicChiralGraphCalculus.lean/2026-07-06_03-43-22_e96488ae.lean`
- `sandbox/ThermodynamicChiralGraphCalculus.lean`
- live owner: `lean/InfoGeometry/Canonical/ThermodynamicChiralGraphCalculus.lean`

Findings:
- the memory snapshot compiles and has 102 declarations with no `sorry`
- the current sandbox file compiles but has 143 declarations and 28 `sorry` occurrences
- maintained live owner `lean/InfoGeometry/Canonical/ThermodynamicChiralGraphCalculus.lean` already exists and compiles
- declaration comparison:
  - every memory-snapshot declaration is present in the live owner (`memory_not_live = []`)
  - the live owner has 137 declarations and zero `sorry`s
  - the live owner additionally contains theorem-honest triangle graph, thermodynamic graph lambda packet, de Bruijn shift graph, and linear-resource sections

Representative live declarations:
- `DirectedThermoGraph`
- `GaugeClosedCycle`
- `gaugeShiftedCycleCurvatureLog_eq_cycleCurvatureLog_add_boundary`
- `cycleCurvatureLog_gauge_invariant`
- `LogWilsonCycleLaw`
- `SchnakenbergDecomposition`
- `logWilsonCycleLaw_of_pos`
- `entropyProductionNonnegOfPointwise`
- `ChiralTriangleRates`
- `ChiralTriangleGraph.graph_cycleCurvatureLog_gauge_invariant`
- `ThermodynamicGraphLambdaPacket`
- `DeBruijnEdge`
- `DecoratedDeBruijnGraph`
- `TracePortSemantics`

Verification:
- `lake env lean agent_memory_recovery/ThermodynamicChiralGraphCalculus.lean/2026-07-06_03-43-22_e96488ae.lean` succeeded
- `lake env lean sandbox/ThermodynamicChiralGraphCalculus.lean` succeeded but emitted `sorry` warnings
- `lake env lean lean/InfoGeometry/Canonical/ThermodynamicChiralGraphCalculus.lean` succeeded with no `sorry` warnings

Conclusion:
- already restored live under a stronger maintained canonical owner
- do not duplicate into the recovery tree
- the sandbox-only declarations absent from live are mostly nontriviality witness/examples or `sorry`-bearing semantic assertions; they should not be restored as closure

### 2.3 Homological probability theorem bank

Fragments inspected:
- `recovered_combined.lean`
- `live_800.lean`
- `agent_memory_recovery/HomologicalProbability.lean/2026-07-06_03-37-11_7b9a3cf6.lean`
- `sandbox/HomologicalProbability.lean`
- live owner: `lean/InfoGeometry/Probability/HomologicalProbability.lean`

Findings:
- maintained live owner `lean/InfoGeometry/Probability/HomologicalProbability.lean` already exists and compiles
- live owner has 130 parsed declarations and zero `sorry`s
- `recovered_combined.lean` is corrupted/non-compiling, but every declaration it parses is already present in the live owner (`recovered_combined_not_live = []`)
- `live_800.lean` and the 800-line memory snapshot are truncated artifacts and fail with unterminated comments
- `sandbox/HomologicalProbability.lean` compiles but emits 16 `sorry` warnings
- sandbox-only names absent from live are `sorry`-bearing or over-assertive semantic theorem shapes, including:
  - `entropicSubadditivity`
  - `homologicalPercolationDuality`
  - `scalarFrequencyNotLinguisticInvariant`
  - `almgrenCycleSpace`
  - `gromovWaist`
  - `scalarCurvatureWidthBound`
  - `quantumStrongSubadditivity`
  - `homologicalProbabilityPrinciple`
  - `homologicalProbabilityMaster`
  - `modularFlowTriviality`
  - `typeIIIRequiresNontracialState`
  - `cartanSplit`
  - `cliffordProbabilityHasClassicalShadow`
  - `infiniteCliffordTypeIII`
  - `affineClosureOwner`
  - `kleinGromovPipeline`

Verification:
- `lake env lean lean/InfoGeometry/Probability/HomologicalProbability.lean` succeeded with no `sorry` warnings
- `lake env lean recovered_combined.lean` failed on missing identifiers and scope/comment corruption around later sections
- `lake env lean live_800.lean` failed with `unterminated comment`
- `lake env lean agent_memory_recovery/HomologicalProbability.lean/2026-07-06_03-37-11_7b9a3cf6.lean` failed with `unterminated comment`
- `lake env lean sandbox/HomologicalProbability.lean` succeeded but emitted 16 `sorry` warnings

Conclusion:
- already restored live under the maintained probability owner
- do not recover the corrupted top-level fragments
- do not promote the sandbox-only `sorry` theorem shapes as restored closure; if any are needed, the orchestrator must formulate precise isolated lemma tasks from current mathlib/repo context

### 2.4 Souriau operatorial log potential

Fragments inspected:
- `sandbox/SouriauOperatorialLogPotential.lean`
- live owner: `lean/InfoGeometry/Canonical/SouriauOperatorialLogPotential.lean`
- finite readback companion: `lean/InfoGeometry/Canonical/SouriauOperatorialLogPotentialFiniteReadback.lean`
- probe: `test_op_potential.lean`

Findings:
- this family is not safe to classify as simply already-live: the maintained live owner currently fails direct source checking
- live owner has 106 parsed declarations and 28 `sorry` occurrences
- sandbox has 86 parsed declarations and 13 `sorry` occurrences; it compiles but still contains open `False := sorry` sockets and vacuous instance witnesses, so it is not a theorem-closure source
- finite readback companion has 4 declarations, zero `sorry`s, and cleanly packages finite arithmetic/thermodynamic readbacks
- sandbox-only declaration names absent from live/readback are proof-field readbacks:
  - `OperatorialExponentialFamily.traceClass_untraced_theorem`
  - `DuhamelOperatorDerivative.higherSimplexOrderedForms_satisfy_theorem`
  These are not analytic closure; they are readbacks from explicit structure fields in the sandbox shape.
- the live owner's direct compile failure is caused by two stale trivial `Unit` instance proofs:
  - `instSouriauNegativeLogRNDerivative.entropy_eq_Phi_add_pairing_Q_beta := by simp`
  - `instMomentMapGeneratingPotential.dPhi_eq_negative_pairing_Q _ := rfl`

Verification:
- `lake env lean lean/InfoGeometry/Canonical/SouriauOperatorialLogPotential.lean` failed at:
  - line 274: `simp made no progress`
  - line 301: `rfl` type mismatch, expected `0 = -instSouriauLieThermoData.pairing () ...`
- `lake env lean sandbox/SouriauOperatorialLogPotential.lean` succeeded but emitted `sorry` warnings
- a temporary copy of the live owner with only the two sandbox-style proof replacements succeeded with exit code 0, while still honestly emitting the existing `sorry` warnings

Non-overwriting artifact written:
- `tools/multisystem/major_restore_non_overwriting/patches/SouriauOperatorialLogPotential_compile_repair.patch`

Patch content:
- replace the failed `by simp` proof with `by change (0 : ℝ) = 0 + 0; norm_num`
- replace the failed `rfl` proof with `by change (0 : ℝ) = - 0; norm_num`

Conclusion:
- genuine compile-repair depletion found, but live owner was not modified in this recovery pass
- the patch artifact is a narrow future integration candidate
- this does not close the 28 explicit `sorry` debts in the live owner
- the finite readback companion is the theorem-honest finite corridor; no infinite analytic theorem is restored or claimed

### 2.5 Souriau metriplectic optimal transport

Fragments inspected:
- `agent_memory_recovery_stitched/SouriauMetriplecticOptimalTransport.lean`
- `sandbox/SouriauMetriplecticOptimalTransport.lean`
- live owner: `lean/InfoGeometry/Canonical/SouriauMetriplecticOptimalTransport.lean`

Findings:
- maintained live owner exists and compiles
- stitched recovery file has exactly the live declaration set (`stitched_not_live = []`)
- live owner has 53 parsed declarations and zero `sorry`s
- stitched recovery file has 53 parsed declarations and zero `sorry`s
- sandbox has 77 parsed declarations and 4 `sorry` occurrences
- every live declaration is present in the sandbox (`live_not_sandbox_count = 0`)
- sandbox-only declarations are 24 concrete instance/example witnesses, including:
  - `instGeneralizedSouriauTemperature`
  - `instSouriauLieThermoData`
  - `instSouriauTransportFlow`
  - `instMetriplecticData`
  - `instOptimalTransportMetricWitness`
  - `instGrandCanonicalThermodynamicBridge`

Verification:
- `lake env lean lean/InfoGeometry/Canonical/SouriauMetriplecticOptimalTransport.lean` succeeded
- `lake env lean agent_memory_recovery_stitched/SouriauMetriplecticOptimalTransport.lean` succeeded
- `lake env lean sandbox/SouriauMetriplecticOptimalTransport.lean` succeeded but emitted warnings, including 4 `sorry` warnings in the concrete instance/example tail

Conclusion:
- already restored live under the maintained canonical owner
- do not duplicate the stitched file into the recovery tree
- do not promote the sandbox-only instance/example tail as theorem closure; it includes `sorry` and mostly vacuous concrete witnesses
- no recovery file or patch artifact is justified for this family

### 2.6 O(4,4) / Pin / Möbius projective stack

Fragments inspected:
- `sandbox/O44PinMobiusProjective.lean`
- live owner: `lean/InfoGeometry/OperatorAlgebra/O44PinMobiusProjective.lean`

Findings:
- maintained live owner exists and compiles
- live owner has 68 parsed declarations, 869 lines, and zero `sorry`s
- sandbox has 73 parsed declarations, 377 lines, and 13 `sorry` occurrences
- the live owner is strictly stronger as an owner surface: it adds the construction-data/compatibility layer absent from the sandbox:
  - `O44PinMobiusProjectiveConstructionData`
  - `O44PinMobiusProjectiveConstructionData.toPinMobiusProjective44`
  - `O44PinMobiusProjectiveCompatibility`
  - `o44PinMobiusProjectiveOwnerTarget`
  - `o44PinMobiusProjective_packet`
- sandbox-only names are concrete example/instance witnesses, including:
  - `embed44to55`
  - `mySplitQuadratic44`
  - `mySplitQuadratic55`
  - `myOrthogonal44`
  - `myOrthogonal55`
  - `myPin44CoverDatum`
  - `myPin55CoverDatum`
  - `myConformalMobius44Extension`
  - `myPinMobiusProjective44`
  - `myPinChiralityActionDatum`
- the sandbox examples are not theorem-honest recovered closure: they use zero quadratic forms, concrete `Fin 8/Fin 10` carriers, and multiple `sorry`s for core obligations such as `q_smul`, nondegeneracy, null embedding, sphere inversion, and chirality action laws
- the sandbox structure shape is older/narrower than the live owner: for example the live `SplitQuadratic44` carries `nondegenerate : Prop` and `signature44 : Prop`, while the sandbox used a functional nondegeneracy field; copying sandbox examples into the live owner would not be a clean restoration

Verification:
- `lake env lean lean/InfoGeometry/OperatorAlgebra/O44PinMobiusProjective.lean` succeeded
- `lake env lean sandbox/O44PinMobiusProjective.lean` succeeded but emitted 13 `sorry` warnings

Conclusion:
- already restored live under a stronger maintained owner
- do not recover the sandbox concrete example tail
- any future concrete `Fin 8/Fin 10` model must be orchestrator-formulated as a new exact matrix/quadratic-form construction task, not copied from the `sorry` sandbox
- no recovery file or patch artifact is justified for this family

### 2.7 Krein--Drazin boundary support

Fragments inspected:
- `sandbox/KreinDrazinBoundarySupport.lean`
- `agent_memory_recovery_stitched/KreinDrazinBoundarySupport.lean`
- live owner: `lean/InfoGeometry/Canonical/KreinDrazinBoundarySupport.lean`

Findings:
- maintained live owner exists and compiles
- live owner has 54 parsed declarations, 750 lines, and zero `sorry`s
- sandbox has 63 parsed declarations, 818 lines, and zero `sorry`s
- all live declaration names are present in the sandbox (`live_not_sandbox = []`)
- stitched recovery parses duplicate declaration names but is syntactically corrupted by splice/overlap damage; it contains a `[STITCHER: MISSING OVERLAP]` marker and a second `import` block in the middle of the file
- sandbox-only declarations are a trivial concrete `ℝ` model under `TrivialModel`, including:
  - `kreinCarrier`
  - `drazinData`
  - `adjointData`
  - `compatibleDrazin`
  - `conformalSymmetry`
  - `preservesBoundary`
  - `trivialDrazinSplit`
  - `trivialKreinAdjoint`
  - `trivialBoundarySupport`
- the sandbox-only `ℝ` model is no-sorry and compiles, but it is a vacuous/trivial demonstrator (`L = 1`, `LD = 1`, `H = 0`, ordinary product form) rather than a missing boundary theorem or nontrivial Drazin/Krein model
- the live owner already contains the theorem-honest structural boundary layer: algebraic Drazin split, Krein carrier/adjoint data, projective Drazin-null rays, conformal symmetry witnesses, KMS weight packet, null-boundary target, restricted radical and normal/conormal support surfaces

Verification:
- `lake env lean lean/InfoGeometry/Canonical/KreinDrazinBoundarySupport.lean` succeeded
- `lake env lean sandbox/KreinDrazinBoundarySupport.lean` succeeded
- `lake env lean agent_memory_recovery_stitched/KreinDrazinBoundarySupport.lean` failed immediately with syntax errors from corrupted splice content and a mid-file `import`

Conclusion:
- already restored live under a maintained canonical owner
- do not recover the corrupted stitched file
- do not promote the sandbox-only trivial `ℝ` model as closure; it may be useful only as a future example/test if separately requested
- no recovery file or patch artifact is justified for this family

## 3. Next truthful restoration move

Continue from `non_scratch_recovery_candidates_round3.json` with the next high-signal family after `KreinDrazinBoundarySupport`.

Recommended next candidates:
- `MobiusGeometry`: compare sandbox/recovery snapshots against current topology/projective Möbius owner context

For each:
1. read the recovered snapshot and current sandbox/live context
2. search maintained `lean/` owners for exact or stronger declarations
3. classify exact-live / stronger-live / stale-probe / genuinely depleted
4. recover only small, compiling, theorem-honest kernels under the recovery tree

## 4. MobiusGeometry family

Sources inspected:
- `lean/InfoGeometry/Topology/MobiusGeometry.lean`
- `sandbox/MobiusGeometry.lean`
- all snapshots under `agent_memory_recovery/MobiusGeometry.lean/`
- `agent_memory_recovery_stitched/MobiusGeometry.lean`
- `agent_writes_recovery_v4/lean/InfoGeometry/Topology/MobiusGeometry.lean`

Findings:
- the live owner has 106 parsed declaration names over 2258 lines
- the `agent_writes_recovery_v4` artifact is only a corrupted 31-line tail
- qualified recovery names initially reported as absent (`pole`, `inv_pole`,
  `discriminant`, and `is_fixed_point`) are present in the live owner
- the sandbox-only `strictly_three_transitive` theorem is already restored
  natively in `MobiusThreeTransitiveRecovered.lean`
- the sandbox `non_parabolic_normal_form` is a `sorry` declaration and omits the
  logically necessary non-identity hypothesis
- `MobiusNonParabolicRecovered.lean` contains the native strengthened theorem
  with `h_nonid : ¬ ∀ z, M.eval z = z`
- both recovered owner modules are imported by `Topology/All.lean`

Verification:
- locked build of `InfoGeometry.Topology.MobiusThreeTransitiveRecovered` and
  `InfoGeometry.Topology.MobiusNonParabolicRecovered` completed successfully
  (1545 jobs)

Conclusion:
- already restored in staged theorem-bearing owner modules
- the archived `sorry` statement must not replace the strengthened native owner
- no additional Mobius recovery file is justified

## 5. Inventory validation and next move

Machine-readable validation is recorded in
`RECOVERY_INVENTORY_VALIDATION.json`.

- all 85 scratch archive files are represented exactly once
- all 250 round-3 candidate paths exist
- neither source inventory records exclusions, caps, timeouts, errors, or
  truncation, so neither is an exhaustive machine audit by itself

Next high-signal unclassified no-sorry family after removing umbrella `All.lean`
snapshots and already classified families:
- `sandbox/LogCftMonodromy.lean`

## 6. LogCftMonodromy family

Sources inspected:
- `sandbox/LogCftMonodromy.lean`
- `lean/InfoGeometry/Clifford/LogCftMonodromy.lean`
- `agent_memory_recovery_stitched/LogCftMonodromy.lean`
- `lean/InfoGeometry/Canonical/LogCftMonodromyBridge.lean`
- `sandbox/RestoreLogCftMonodromyBridge.lean`
- Git history and the staged owner diff

Findings:
- the sandbox is a complete no-`sorry` 503-line owner snapshot and compiles
- the maintained live owner had equivalent bundled theorem strength but omitted
  four reusable coordinate declarations present in the sandbox:
  - `hadjiivanovMonodromy_pow_00`
  - `hadjiivanovMonodromy_pow_01`
  - `hadjiivanovMonodromy_pow_10`
  - `hadjiivanovMonodromy_pow_11`
- no other maintained owner or stitched snapshot exported those names
- the four declarations were restored directly beside
  `hadjiivanovMonodromy_pow_winding`
- `hadjiivanovMonodromy_genuine_coefficient_readout` now consumes the restored
  coordinate theorems instead of reproving their bodies anonymously
- the restoration changes no definitions and introduces no new hypotheses
- live/sandbox declaration parity is now exact: 54 names each, with no
  declaration-name difference in either direction

Verification:
- locked owner/canonical bridge build completed successfully (8034 jobs)
- locked build of all 12 direct owner dependers completed successfully
  (8340 jobs)
- axiom audit of all four restored readouts and the bundled theorem reports only
  `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`
- targeted `git diff --check` passed

Conclusion:
- genuinely depleted reusable owner API restored from a compiling archive
- restoration is theorem-honest and downstream-compatible
