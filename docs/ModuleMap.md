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

Current state:

- transport is real
- realized generalized-metric projector factorization is now explicit
- the strongest maintained-projector identification is not fully derived yet

### If you want the KKT / defect / conformal branch

Read:

1. [KKTCore.lean](../lean/InfoGeometry/Canonical/KKTCore.lean)
2. [EPDefectAlgebra.lean](../lean/InfoGeometry/Canonical/EPDefectAlgebra.lean)
3. [KKTGeneralizedInverseBridge.lean](../lean/InfoGeometry/Canonical/KKTGeneralizedInverseBridge.lean)
4. [PhaseSpaceConformalKKTBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpaceConformalKKTBridge.lean)
5. [PhaseSpaceCausalFlowBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpaceCausalFlowBridge.lean)

### If you want the Weyl / anomaly branch

Read:

1. [ConformalAnomalySource.lean](../lean/InfoGeometry/Canonical/ConformalAnomalySource.lean)
2. [WeylGaugeField.lean](../lean/InfoGeometry/Canonical/WeylGaugeField.lean)
3. [WeylTransport.lean](../lean/InfoGeometry/Canonical/WeylTransport.lean)
4. [WeylTransportChiralBridge.lean](../lean/InfoGeometry/Canonical/WeylTransportChiralBridge.lean)
5. [PhaseSpaceWeylCausalBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpaceWeylCausalBridge.lean)

Current state:

- the branch now has an explicit operator package (`SourceSpineAndWeylEndpoint`) carrying dilation source, obstruction grade/block structure, and holonomy endpoint
- the primary theorem package is now in-source and no longer just scalar prose
- the next step is reducing explicit commutation/identification hypotheses where possible

### If you want the Tomita / modular transport branch

Read:

1. [TomitaTakesaki.lean](../lean/InfoGeometry/Canonical/TomitaTakesaki.lean)
2. [BogoliubovTransport.lean](../lean/InfoGeometry/Canonical/BogoliubovTransport.lean)
3. [ConnesArakiTomita.lean](../lean/InfoGeometry/Canonical/ConnesArakiTomita.lean)

This branch is currently more mature than the KK/index branch.

### If you want the split Clifford / KK frontier

Read:

1. [ClNN.lean](../lean/InfoGeometry/Clifford/ClNN.lean)
2. [ClNNSpecialization.lean](../lean/InfoGeometry/Clifford/ClNNSpecialization.lean)
3. [ClNNBottBridge.lean](../lean/InfoGeometry/Canonical/ClNNBottBridge.lean)
4. [ClNNFredholmBridge.lean](../lean/InfoGeometry/KK/ClNNFredholmBridge.lean)

Current state:

- the split `Cl(n,n)` presentation is real
- the KK bridge is still thin
- there is no native index-anomaly weld yet

## Current Structural Picture

### Semantic roots

Treat these as the main roots:

- [PositiveMeasure.lean](../lean/InfoGeometry/PositiveMeasure.lean)
- [PositiveRayCore.lean](../lean/InfoGeometry/Canonical/PositiveRayCore.lean)
- [RelativePotentialCore.lean](../lean/InfoGeometry/Canonical/RelativePotentialCore.lean)
- [NeutralPhaseSpaceCore.lean](../lean/InfoGeometry/Clifford/NeutralPhaseSpaceCore.lean)
- [PhaseSpaceGeneralizedMetric.lean](../lean/InfoGeometry/Clifford/PhaseSpaceGeneralizedMetric.lean)
- [KKTCore.lean](../lean/InfoGeometry/Canonical/KKTCore.lean)
- [TomitaTakesaki.lean](../lean/InfoGeometry/Canonical/TomitaTakesaki.lean)

### Compatibility scaffolds

Treat these as useful but non-root:

- [ClNN.lean](../lean/InfoGeometry/Clifford/ClNN.lean)
- [GeneralizedMetricBField.lean](../lean/InfoGeometry/Clifford/GeneralizedMetricBField.lean)
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
2. strengthen the source-driven Weyl package by removing explicit commutation/identification hypotheses where possible
3. attach the count/projective trunk to the corrected phase-space trunk at the polarized junction
4. add one twisted end-to-end finite-dimensional example
5. tighten operator anomaly to modular source/sink closure as a first-class bridge lane

This is the current practical roadmap encoded by the codebase.
