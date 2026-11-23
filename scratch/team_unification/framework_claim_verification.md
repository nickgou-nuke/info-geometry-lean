# Independent source verification: unified GNS / matrix / state framework

**Scope.** Read repo-owned Lean definitions, imports, and theorem bodies in the isolated `framework_verifier` worktree; additionally read the current root-worktree source of the staged `CantorBernoulliFiniteDiagonalGNSBridge` and its supporting staged owners to verify those candidate claims. The isolated checkout does not contain the root staged changes at its HEAD, so the candidate-specific observations below are explicitly based on the root source paths inspected. No builds, Lean checks, source edits, graph refreshes, or database writes were performed. This report is the only new file created.

## Findings at a glance

- **Generic filtered GNS infrastructure exists.** Restriction along `StarAlgHom` yields pre-GNS and completed-GNS isometries; compatible state families yield coherent isometric GNS transitions and a complete Hilbert colimit. A separate generic theorem descends those stages to the target GNS space from a supplied star-algebra cocone and target state. There is also a `StarAlgHom` representation of an *algebraic star direct limit* on the global GNS Hilbert colimit.
- **The finite concrete BitWord representation is both linear and, in a separate owner, a `StarAlgHom`.** Do not confuse `bitWordMatrixLinearRepresentation : … →ₗ[ℂ] …` in the matrix readout owner with `bitWordMatrixStarRepresentation : … →⋆ₐ[ℂ] …` in the star-representation owner. The latter is an actual finite-stage multiplicative, unital, scalar-compatible, star-preserving homomorphism into `BoundedL2Operator`; neither declaration alone is an infinite C⋆-completion representation.
- **Several naturality squares are explicit.** Generic GNS transition/composition/intertwining and colimit inclusion squares are proved; native matrix reindexing/tower, trace, and candidate diagonal-readout squares are also proved. State exactly which carriers each square connects.
- **Spatial and gauge readouts agree on diagonal cylinder/projection data, not as unrestricted states on a common completed algebra.** Source also provides a spatial nonfaithfulness witness and separate gauge word-kernel calculations. No full spatial-state = gauge-state or resulting GNS-equivalence theorem was found in the inspected owners.

## Generic GNS transport and colimit results

### Restriction and filtered transitions

In `lean/InfoGeometry/Canonical/FilteredGNSRepresentation.lean`, namespace `CStarStateColimit.Native.FilteredGNS`:

- `restricted_star_mul` and `restricted_star_square` state that restricting a target `State B` along `f : A →⋆ₐ[ℂ] B` transports the full GNS sesquilinear/quadratic kernel.
- `preGNSMap` maps the restricted-state pre-GNS space to the target-state pre-GNS space. `preGNSMap_inner_toPreGNS` establishes inner-product preservation on generators; `preGNSMap_inner` extends it to all pre-GNS elements; `preGNSLinearIsometry` packages the isometry.
- `gnsMap` and `gnsMapCLM` are the completed transport. `gnsMap_isometry`, `gnsMap_toPreGNS`, and `gnsMap_intertwines` prove completed-space isometry, generator readback, and representation intertwining. `gnsMap_comp_toPreGNS` proves composition on canonical algebraic vectors; its statement is deliberately only on that dense subspace.
- For `ContinuousStarInductiveSystem` plus a `CompatibleStateFamily`, `filteredGNSMap` and `filteredGNSMapCLM` give the stage transitions. The source proves `filteredGNSMap_isometry`, `filteredGNSMap_intertwines_toPreGNS`, `filteredGNSMap_intertwines`, identity (`filteredGNSMap_id_toPreGNS`, `filteredGNSMap_id`) and composition (`filteredGNSMap_comp_toPreGNS`, `filteredGNSMap_comp`).
- `gnsDirectInductiveSystem` and `gnsModuleDiagram` package this as a direct system and `ModuleCat` diagram. `GNSModuleColimit` is the native ModuleCat colimit; `gnsColimitInclusion_transition` proves the canonical inclusion square, and `gnsColimitInclusion_representation_compat` proves representation compatibility after transition.

In `FilteredGNSHilbertColimit.lean`, namespace `CStarStateColimit.Native.FilteredGNSHilbertColimit`, `filteredGNSIsometricDirectSystem` obtains identity/composition from the generic GNS results; `AlgebraicGNSHilbertColimit` and `GNSHilbertColimit` are the algebraic direct limit and its Hilbert completion. `gnsStageToHilbertColimit_transition`, `dense_iUnion_range_gnsStageToHilbertColimit`, and `gnsHilbertColimit_complete` prove transition coherence, dense stage images, and completeness.

### Generic target descent versus algebraic representation

- `FilteredGNSColimitRepresentation.lean` assumes a `StarInductiveCocone` into a C⋆ algebra `Ainf` and a normalized positive `State Ainf` (`Ω`). `restrictedStateFamily` is induced by restricting `Ω`; `stageTargetGNSMap_transition` proves the stage-to-target square on the completed spaces. `gnsTargetInductiveCocone` and `gnsTargetModuleCocone` make the target cocone; `descendGNSColimit` is the universal **linear map** from the native GNS ModuleCat colimit to `Ω.functional.GNS`. `descendGNSColimit_stage`, `descendGNSColimit_representation`, and `descendGNSColimitHom_unique` give stage restriction, represented-observable intertwining, and uniqueness. This owner does not itself state that the descent is onto or isometric.
- Separately, `FilteredGNSAlgebraicColimitRepresentation.lean` defines `algebraicColimitGNSRepresentation : AlgebraicStarDirectLimit Stage sys →⋆ₐ[ℂ] (GNSHilbertColimit … →L[ℂ] GNSHilbertColimit …)`. `algebraicColimitGNSRepresentation_of`, `_stage`, and `_unique` prove its restrictions and uniqueness. It is a representation of the algebraic star direct limit, not a declaration that a C⋆-algebra colimit/completion has been built.
- Related faithful-range / represented-range owners exist (`FilteredGNSFaithfulCStarRepresentation`, `FilteredGNSRepresentedCStarTopology`), but their represented-range completion equivalence is a distinct construction; it should not be attributed to `descendGNSColimit`.

These distinctions follow the actual carriers. `FilteredGNSColimitRepresentation` explicitly uses a ModuleCat colimit and requires the target C⋆ cocone/state as inputs; the generic results do not conjure a target infinite Cuntz algebra or its state.

## Finite matrix representation: actual interface

`OperatorAlgebra/CantorBernoulliFiniteMatrixRepresentationBridge.lean` defines

`bitWordMatrixLinearRepresentation : BitWordMatrixStage n →ₗ[ℂ] BoundedL2Operator`.

It proves linearity, matrix-unit images, identity sum, and star compatibility on matrix units (`bitWordMatrixLinearRepresentation_star_single`). **Its interface is only linear**, and the general multiplication/star laws are not fields of this definition.

However, the separate owner `OperatorAlgebra/CantorBernoulliFiniteMatrixStarRepresentationBridge.lean` defines

`bitWordMatrixStarRepresentation : BitWordMatrixStage n →⋆ₐ[ℂ] BoundedL2Operator`.

The construction explicitly proves `map_one'`, `map_mul'`, `map_zero'`, `map_add'`, `commutes'`, and `map_star'`, then `bitWordMatrixStarRepresentation_apply_single` gives the matrix-unit readout. `CantorBernoulliFiniteMatrixRepresentationRefinementBridge.bitWordMatrixStarRepresentation_refinement` proves the successor refinement for its explicit `dyadicMatrixEmbedding`. `CuntzBoundaryMatrixStageBridge.boundaryRep` is an abbrev to this `StarAlgHom`, with `matrixUnit_generator_transport` and `boundaryRep_diagonal` readbacks.

Thus “the concrete finite matrix representation is merely linear” is false if referring to the complete repo-owned finite-stage construction; it is accurate only for the interface in `FiniteMatrixRepresentationBridge`. Conversely, “the StarAlgHom proves a completed infinite representation” overstates its scope.

## Explicit transition/naturality squares

1. **BitWord and standard finite matrix towers:** `BitWordComplexCStarTowerNaturalityBridge.stageStarAlgEquiv` is a `StarAlgEquiv`. `stageStarAlgEquiv_bond` proves the commuting square from `ComplexMatrixStage.bondFun` to `concreteStep`; `stageStarAlgEquiv_normalizedTrace` and `stageStarAlgEquiv_bond_trace` prove normalized-trace transport and its successor compatibility.
2. **Native C⋆ matrix stages:** `CantorBernoulliCStarMatrixTraceState.cstarConcreteMap` is a `StarAlgHom`; `cstarConcreteMap_toMatrixStage` reads it back as `concreteMap` (proof `rfl`). `cstarMatrixInductiveSystem` proves identity/composition. `cstarMatrixTraceState_transition`, `_restrict`, and `_transition_general` prove state compatibility; `cstarMatrixTraceStateFamily` packages the compatible state family.
3. **Native C⋆ stage to BitWord stage (candidate source):** `CantorBernoulliFiniteDiagonalGNSBridge.cstarStageToBitWordStage` is a `StarAlgEquiv`. `cstarStageToBitWordStage_succ` proves the successor square, explicitly using `stageStarAlgEquiv_bond` and `cstarConcreteMap_toMatrixStage`. `gaugeStateFamily_canonical_bitWord_matrix_readout` identifies the finite gauge trace with the canonical reindexed matrix trace.
4. **Diagonal cylinder readout:** `cstarDiagonalCylinderLinearMap_succ` proves the finite C⋆ successor square for the composite `cstarStageToBitWordStage → diagonalPart → diagonalCylinderL2`; it uses `cstarStageToBitWordStage_succ`, `diagonalPart_bond_compatible`, and `diagonalCylinderL2_compatible_succ`.
5. **GNS-stage readout and colimit:** the candidate `gaugeDiagonalGNSMap_transition_succ` proves compatibility of the completed finite-stage GNS maps on all vectors by extending the generator check from the dense PreGNS image; `gaugeDiagonalGNSMap_transition` proves all `m ≤ n` by induction and the generic GNS composition law. `gaugeDiagonalGNSColimitStageMap_compatible` then builds `gaugeDiagonalGNSAlgebraicColimitMapReal`; `gaugeDiagonalGNSAlgebraicColimitMap` is the complex-linear descent to the algebraic module direct limit. `gaugeDiagonalGNSAlgebraicColimitMap_norm_le` proves contractivity; `gaugeDiagonalGNSAlgebraicColimitMapCLM` and `gaugeDiagonalGNSHilbertColimitMap` pass to a bounded map and continuous extension. `_stage` theorems preserve finite-stage readouts. `gaugeDiagonalGNSHilbertColimitMap_denseRange` proves dense range using the dense cylinder carrier.

The last map is a diagonal readout from the full noncommutative GNS colimit into boundary `L²`; it is not claimed to be injective/isometric or a unitary identification. Its domain is not replaced by the diagonal algebra; rather, the map factors through diagonal extraction, and off-diagonal matrix coefficients are discarded.

## Spatial state versus gauge state

- `CantorBernoulliSpatialCylinderStateBridge.spatialState_eq_canonicalGaugeState_on_projection` proves equality on each `operatorCylinderProjection w`. The same owner proves the spatial cylinder value is the Bernoulli branch measure.
- `CuntzBoundaryMatrixStageBridge.spatialState_boundaryRep_diagonal_eq_matrixTrace` proves the spatial state on `boundaryRep n (Matrix.diagonal f)` equals the normalized BitWord matrix trace. `CantorBernoulliFiniteMatrixRepresentationBridge.bitWordMatrixGaugeReadout_eq_trace` and `CantorBernoulliGaugeFilteredGNSColimitBridge.gaugeStateFamily_bitWord_matrix_readout` give the matching finite gauge/matrix-trace readout. The staged candidate further proves `gaugeStateFamily_diagonal_projective_integral` and `spatialState_boundaryRep_diagonal_projective_integral`: both evaluate finite diagonal observables as the same projective-limit Bernoulli integral.
- The equality is restriction-level: diagonal observables / cylinder projections. The spatial-cylinder owner explicitly says it does not identify values on off-diagonal Cuntz word monomials.
- The source carries separate spatial and gauge objects. `CantorBernoulliGeneratedCStarSpatialStateBridge.generatedSpatialState` is the restriction of the constant-vector spatial state to the generated C⋆ subalgebra. `generatedSpatialState_not_faithful_witness` gives a nonzero annihilator with zero spatial-state quadratic value. The gauge-word side has `CantorBernoulliContinuousStateGNSBridge.gaugeStateWord_annihilator_normSq` (the corresponding canonical gauge-word quadratic combination evaluates to 1). These results support the distinction; they are not a theorem identifying two states on one common completed carrier. `CantorBernoulliSpatialCuntzGNSBridge.spatialCuntzGNS_expectation_recovery` concerns the spatial state’s own GNS representation, not the gauge GNS representation.

## Scoped open points and verification limit

- The generic owners prove GNS transport/colimit properties under their explicit C⋆ stage, compatible-state, cocone, and target-state hypotheses. No universal target cocone/state is constructed by those generic lemmas.
- The candidate diagonal GNS-to-`L²` map proves contractivity, stage compatibility, dense range, and finite diagonal readback. It does not claim full-GNS isometry/unitarity; the proof factors through diagonal extraction, so off-diagonal content is not retained.
- The finite matrix StarAlgHom and matrix tower naturality are fully stated at finite stages. No conclusion about a completed full Cuntz C⋆-algebra follows solely from them.
- Spatial/gauge equality is established on the named diagonal/projection subalgebra only. No full equality or GNS equivalence appears in the owners inspected. This is an owner-scoped observation, not a repo-wide nonexistence claim.
- This is an independent source audit, not kernel/build certification; no axiom-print output was run or interpreted.
