# Phase 1 UHF trace-state / GNS-colimit audit

## Verdict

The requested Phase 1 connection is already present in repo-owned Lean source, most directly in `InfoGeometry.Canonical.CantorBernoulliGaugeFilteredGNSColimitBridge`. No new theorem/file is justified by this source audit. Do not duplicate that bridge. This is a source audit only: no Lean build was run, so this report does not certify current kernel verification.

## Ground-truth contract

- **Carrier:** finite operator-norm C*-matrix stages `CStarMatrixStage n := CStarMatrix (Fin (2^n)) (Fin (2^n)) ℂ`, with maps `cstarConcreteMap`; the underlying matrix stages use `Matrix (Fin (2^n)) (Fin (2^n)) ℂ`.
- **State:** each stage carries the normalized matrix trace, `cstarMatrixTraceState n`, represented as a native `CStarStateColimit.Native.State` whose functional is a Mathlib `PositiveLinearMap`.
- **Compatibility:** `cstarMatrixTraceStateFamily` inhabits `ContinuousStarInductiveSystem.CompatibleStateFamily CStarMatrixStage cstarMatrixInductiveSystem`.
- **Colimit:** `gaugeGNSHilbertColimit` is the existing generic `GNSHilbertColimit gaugeStage gaugeSystem gaugeStateFamily`; finite-stage GNS inclusions are isometric, transition-compatible, dense in the colimit, and the colimit is complete.
- **Finite gauge readout:** under the explicit `BitWord n ≃ Fin (2^n)` indexing, the normalized trace of a matrix unit agrees with `canonicalGaugeState (List.ofFn u) (List.ofFn v)`. The GNS vacuum recovers that functional on these units and on arbitrary stage observables.

## Owner declarations inspected

1. `Canonical/CuntzMatrixTowerInstantiation.lean`
   - `MatrixStage n := Matrix (Fin (2^n)) (Fin (2^n)) ℂ`.
   - `matrixTraceFunctional n` is `(1 / (2^n : ℂ)) • Matrix.traceLinearMap ...`; `matrixTraceState n` is its evaluation.
   - `matrixTraceState_one`, `matrixTraceState_nonneg`, and `matrixTraceState_mul_comm` establish finite normalized-trace facts at the raw matrix carrier.

2. `Canonical/CuntzMatrixTraceTower.lean`
   - `concreteStep n` is the star-algebra embedding induced by `A ↦ A ⊗ₖ 1`, reindexed from `Fin (2^n) × Fin 2` to `Fin (2^(n+1))`.
   - `concreteStep_trace` gives `trace(concreteStep n A) = 2 * trace A`; `concreteData.trace_compatible`, `concreteMap_comp`, and `concreteMap_trace` establish normalized-trace compatibility across all `i ≤ j`.

3. `Canonical/CantorBernoulliCStarMatrixTraceState.lean`
   - `CStarMatrixStage n` is the finite Mathlib C*-matrix type-copy.
   - `cstarConcreteMap` transports the concrete matrix maps; `cstarMatrixInductiveSystem` proves identity and composition laws.
   - `cstarMatrixPositiveTraceFunctional` is the native positive map; `cstarMatrixTraceState` is normalized.
   - `cstarMatrixTraceState_transition_general` proves state evaluation is compatible for any `i ≤ j`; `cstarMatrixTraceStateFamily` packages exactly the required `CompatibleStateFamily`.
   - Also proved here: finite-stage faithful trace state, the induced topological-colimit scalar readout, and its equality with the compatible continuous readout.

4. `Canonical/CantorBernoulliGaugeFilteredGNSColimitBridge.lean`
   - `gaugeStage := CStarMatrixStage`, `gaugeSystem := cstarMatrixInductiveSystem`, and `gaugeStateFamily := cstarMatrixTraceStateFamily` are direct aliases to the above concrete data.
   - `gaugeGNSHilbertColimit` and `gaugeGNSStageToColimit` instantiate the generic `FilteredGNSHilbertColimit` owner with that family.
   - `gaugeGNSStageToColimit_transition`, `gaugeGNSStageToColimit_norm`, `dense_iUnion_range_gaugeGNSStageToColimit`, and `gaugeGNSHilbertColimit_complete` provide the requested GNS-colimit connection.
   - `gaugeStateFamily_bitWord_matrix_unit` proves the bit-word matrix-unit/gauge-kernel readout; `gaugeGNSStage_bitWord_matrix_unit_expectation` transports it to the finite-stage GNS vacuum. `gaugeGNSStage_matrix_expectation` covers arbitrary finite-stage observables.

5. Supporting bridge owners:
   - `Canonical/CantorBernoulliFiniteMatrixGaugeTraceBridge.lean`: `bitWordIndexEquiv` and `matrixTraceState_bitWordUnit_eq_canonicalGaugeState` give the exact finite matrix-unit formula.
   - `OperatorAlgebra/CantorBernoulliFiniteMatrixUnitBridge.lean`: defines the BitWord matrix carrier, normalized trace, trace on matrix units, operator matrix-unit relations/refinement, and finite diagonal trace readouts. Its header explicitly does not assert a matrix-algebra isomorphism or infinite UHF state.
   - `Canonical/CantorBernoulliDiagTraceBridge.lean`: `projectiveLimitMeasure_integral_prefix_eq_DiagTrace` identifies finite-prefix integration with normalized diagonal trace; it does not extend the state to a completed Cuntz algebra.

## Spatial state is a different object

- `OperatorAlgebra/CantorBernoulliSpatialNativeStateBridge.lean` defines `spatialPositiveFunctional` and normalized `spatialState` on the concrete bounded operators of the Bernoulli-boundary L² space.
- `OperatorAlgebra/CantorBernoulliSpatialCylinderStateBridge.lean` proves the spatial functional on a cylinder projection is its Bernoulli cylinder mass, hence agrees with the gauge word kernel on **diagonal projections only**. Its module comment explicitly disclaims off-diagonal identification.
- `OperatorAlgebra/CantorBernoulliSpatialNonSeparatingBridge.lean` proves a nonzero spatial annihilator with zero spatial `A* A` expectation; the spatial state is not faithful. By contrast, `cstarMatrixTraceState_faithful` proves faithfulness at each finite matrix stage. These facts reinforce that the constructions must not be merged.
- The gauge word kernel is a finite word/matrix-unit readout here, not an assertion that the spatial vector state equals a completed infinite-algebra gauge state.

## Boundary of the Cuntz-specific colimit owner

`Canonical/CStarAlgebraStateColimit.lean` defines the generic `CompatibleStateFamily` and its restriction/evaluation laws. `Canonical/CuntzGNSFilteredSystem.lean` and `Canonical/UHFCuntzGNSColimit.lean` specialize the GNS colimit to an input `CuntzStarTower Stage` plus a compatible family; they do not supply a concrete tower/state themselves. `Canonical/CuntzStarInductiveSystem.lean` requires a finite-stage Cuntz family and transition maps preserving its generators. The concrete finite UHF matrix stages above are **not** asserted to be such a Cuntz tower; `Canonical/MatrixCuntzStarTower.lean` records the finite-matrix obstruction to stagewise Cuntz-2 isometries. Thus the concrete trace family is connected to the generic filtered GNS-colimit owner, not to a claimed finite-matrix `CuntzStarTower` instantiation. Do not force that type-level connection.

## Smallest remaining boundary / adjacent claims

For the stated Phase 1 (finite compatible UHF trace family → existing generic filtered GNS Hilbert colimit, with finite gauge readouts), no source-confirmed gap remains in the inspected owners. If “GNS-colimit owner” was intended specifically to mean `UHFCuntzGNSColimit`, clarify that target: the matrix stages here do not instantiate its `CuntzStarTower` input, and the finite-matrix obstruction warns against claiming they do.

Not established by this Phase 1 connection: an infinite UHF C*-completion with an extended state; a completed Cuntz-algebra positive state extending the word kernel; a full Cuntz KMS condition/dynamics; equality of the spatial and gauge functionals off diagonal; identification of this UHF GNS colimit with a Cuntz GNS colimit; or a Tomita–Takesaki operator/modular theorem.

## Search and verification scope

Searched repo-owned `lean/InfoGeometry/{Canonical,OperatorAlgebra}` for `CompatibleStateFamily`, the concrete trace-family and gauge/GNS declaration names, `CuntzStarTower`, and their dependents. The search located further consumers including `Canonical/CantorBernoulliFiniteDiagonalGNSBridge.lean` and `Canonical/Cl11TraceGNSHilbertColimitBridge.lean`; these are not evidence for infinite C*-completion. No graph refresh/write or external-reference proof source was used. No build was run per task instruction; kernel/build freshness is unverified here.
