# Module Map

This page is the practical navigation map for the current codebase.
For document status, start with [RepositoryMemoryMap.md](RepositoryMemoryMap.md).
For truth, trust Lean source first.

## Entry Surfaces

These top-level files have different roles:

| File | Use it when |
|---|---|
| [lean/InfoGeometry.lean](../lean/InfoGeometry.lean) | you want the published library entrypoint |
| [lean/InfoGeometry/Library.lean](../lean/InfoGeometry/Library.lean) | you want the stable canonical publication surface |
| [lean/InfoGeometry/Canonical/All.lean](../lean/InfoGeometry/Canonical/All.lean) | you want the stable canonical umbrella |
| [lean/InfoGeometry/All.lean](../lean/InfoGeometry/All.lean) | you want the full project umbrella |
| [lean/InfoGeometry/Audit.lean](../lean/InfoGeometry/Audit.lean) | you want the architecture and vacuity enforcement entry surface |
| [lean/InfoGeometry/Meta/Architecture.lean](../lean/InfoGeometry/Meta/Architecture.lean) | you need the representation-depth grammar and policy tags |

## Current Major Families

| Area | Role | Good first file |
|---|---|---|
| positive measure / projective normalization | lower seed line for counts and gauge | [PositiveMeasure.lean](../lean/InfoGeometry/PositiveMeasure.lean) |
| canonical relative-potential and operator lift | current clean count-to-operator corridor | [RelativePotentialCore.lean](../lean/InfoGeometry/Canonical/RelativePotentialCore.lean) |
| corrected phase-space / Clifford | corrected owner lane on `E × E*` | [NeutralPhaseSpaceCore.lean](../lean/InfoGeometry/Clifford/NeutralPhaseSpaceCore.lean) |
| doubled / Krein / chirality | realized carrier and sheet geometry | [DoubledSpace.lean](../lean/InfoGeometry/Krein/DoubledSpace.lean) |
| generalized metric / chirality / recomposition | current branch junction from corrected owner to maintained leaves | [PhaseSpaceGeneralizedMetric.lean](../lean/InfoGeometry/Clifford/PhaseSpaceGeneralizedMetric.lean) |
| KKT / inverse-kernel / conformal | grade decomposition and defect algebra | [KKTCore.lean](../lean/InfoGeometry/Canonical/KKTCore.lean) |
| Tomita / Bogoliubov / Weyl | modular and transport branches | [TomitaTakesaki.lean](../lean/InfoGeometry/Canonical/TomitaTakesaki.lean) |
| Quantum Geometric Tensor (QGT) / Anomaly | metric readout and operator transport | [GeometricTensorOperatorLift.lean](../lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean) |
| Bulk-Boundary / Majorana / Kitaev | boundary regularization and zero-mode pairs | [BulkBoundary.lean](../lean/InfoGeometry/Quantum/BulkBoundary.lean) |
| DAG / infra / docs tooling | graph export, reports, and refresh workflow | [lean/DAG/README.md](../lean/DAG/README.md) |

## Read By Task

### If you want the cleanest current theorem corridor

Read:

1. [PositiveMeasure.lean](../lean/InfoGeometry/PositiveMeasure.lean)
2. [Normalize.lean](../lean/InfoGeometry/Projective/Normalize.lean)
3. [PositiveRayCore.lean](../lean/InfoGeometry/Canonical/PositiveRayCore.lean)
4. [RelativePotentialCore.lean](../lean/InfoGeometry/Canonical/RelativePotentialCore.lean)
5. [RelativePotentialCountBridge.lean](../lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean)
6. [RelativeSurprisalOperatorLift.lean](../lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean)

This is still the cleanest nonvacuous adjacent corridor in the repo.

### If you want the current main geometric trunk

Read:

1. [NeutralPhaseSpaceCore.lean](../lean/InfoGeometry/Clifford/NeutralPhaseSpaceCore.lean)
2. [NeutralPhaseSpaceDoubledBridge.lean](../lean/InfoGeometry/Clifford/NeutralPhaseSpaceDoubledBridge.lean)
3. [PhaseSpaceGeneralizedMetric.lean](../lean/InfoGeometry/Clifford/PhaseSpaceGeneralizedMetric.lean)
4. [PhaseSpaceGeneralizedMetricChiralityBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpaceGeneralizedMetricChiralityBridge.lean)

This is the corrected owner lane.

### If you want the recomposition branch

Read:

1. [PhaseSpacePolarizedBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpacePolarizedBridge.lean)
2. [PhaseSpaceRecompositionBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpaceRecompositionBridge.lean)
3. [RelativeModularPolarizedBridge.lean](../lean/InfoGeometry/Canonical/RelativeModularPolarizedBridge.lean)
4. [RelativeModularRecomposition.lean](../lean/InfoGeometry/Canonical/RelativeModularRecomposition.lean)
5. [RelativeModularSingularization.lean](../lean/InfoGeometry/Canonical/RelativeModularSingularization.lean)

Current state:

- transport is real
- realized generalized-metric projector factorization is now explicit
- modular singularization for boundary modes is now active

### If you want the KKT / defect / conformal branch

Read:

1. [KKTCore.lean](../lean/InfoGeometry/Canonical/KKTCore.lean)
2. [EPDefectAlgebra.lean](../lean/InfoGeometry/Canonical/EPDefectAlgebra.lean)
3. [KKTGeneralizedInverseBridge.lean](../lean/InfoGeometry/Canonical/KKTGeneralizedInverseBridge.lean)
4. [PhaseSpaceConformalKKTBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpaceConformalKKTBridge.lean)
5. [PhaseSpaceCausalFlowBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpaceCausalFlowBridge.lean)

### If you want the Weyl / anomaly / QGT branch

Read:

1. [ConformalAnomalySource.lean](../lean/InfoGeometry/Canonical/ConformalAnomalySource.lean)
2. [EinsteinAnomalyOperator.lean](../lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean)
3. [GeometricTensorOperatorLift.lean](../lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean)
4. [WeylTransport.lean](../lean/InfoGeometry/Canonical/WeylTransport.lean)
5. [PhaseSpaceWeylCausalBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpaceWeylCausalBridge.lean)

Current state:

- the branch has an explicit operator package carrying dilation source and holonomy
- Einstein anomaly is lifted to the doubled carrier
- Quantum Geometric Tensor metric readout is derived from operator transport commutators

### If you want the Tomita / modular transport branch

Read:

1. [TomitaTakesaki.lean](../lean/InfoGeometry/Canonical/TomitaTakesaki.lean)
2. [BogoliubovTransport.lean](../lean/InfoGeometry/Canonical/BogoliubovTransport.lean)
3. [TransportLieDerivative.lean](../lean/InfoGeometry/Canonical/TransportLieDerivative.lean)

This branch now includes explicit infinitesimal transport laws via Lie derivatives.

### If you want the Bulk-Boundary / Majorana frontier

Read:

1. [BulkBoundary.lean](../lean/InfoGeometry/Quantum/BulkBoundary.lean)
2. [BulkBoundaryRegularizationBridge.lean](../lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean)
3. [MajoranaKitaevSpinorBridge.lean](../lean/InfoGeometry/Canonical/MajoranaKitaevSpinorBridge.lean)

Current state:

- boundary regularization via generalized inverses (Drazin/Moore-Penrose) is real
- Weyl boundary zero-mode pairs are explicitly identified for Kitaev chains

## Current Structural Picture

### Semantic roots

Treat these as the main roots:

- [PositiveMeasure.lean](../lean/InfoGeometry/PositiveMeasure.lean)
- [PositiveRayCore.lean](../lean/InfoGeometry/Canonical/PositiveRayCore.lean)
- [RelativePotentialCore.lean](../lean/InfoGeometry/Canonical/RelativePotentialCore.lean)
- [NeutralPhaseSpaceCore.lean](../lean/InfoGeometry/Clifford/NeutralPhaseSpaceCore.lean)
- [PhaseSpaceGeneralizedMetric.lean](../lean/InfoGeometry/Clifford/PhaseSpaceGeneralizedMetric.lean)
- [KKTCore.lean](../lean/InfoGeometry/Canonical/KKTCore.lean)
- [GeometricTensorOperatorLift.lean](../lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean)
- [BulkBoundary.lean](../lean/InfoGeometry/Quantum/BulkBoundary.lean)

### Compatibility scaffolds

Treat these as useful but non-root:

- [RelativeModularBerezinianBridge.lean](../lean/InfoGeometry/Canonical/RelativeModularBerezinianBridge.lean)
- [MajoranaKitaevSpinorBridge.lean](../lean/InfoGeometry/Canonical/MajoranaKitaevSpinorBridge.lean)
- [GeneralizedMetricPolarizedBridge.lean](../lean/InfoGeometry/Canonical/GeneralizedMetricPolarizedBridge.lean)

## What To Ignore At First

Do not start with:

- `docs/auto/index.md`
- `reports/dag/*`
- synthesis docs under `docs/`
- umbrella files only

Those are useful later. They are not the first proof surface.

## Current Open Junctions

The next real gaps are:

1. derive the realized-projector to maintained tomita-projector identification
2. attach the count/projective trunk to the corrected phase-space trunk at the polarized junction
3. add one twisted end-to-end finite-dimensional example
4. tighten the response matrix to the Weyl anomaly readout for grand-canonical models
5. formalize the spinor-modular identification theorem (currently in the "sorry-equivalent" layer)

This is the current practical roadmap encoded by the codebase.
