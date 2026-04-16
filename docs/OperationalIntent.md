# Operational Intent

This repository is one theory with several presentations.
The main burden is not to flatten those presentations into one file-level story,
but to make the morphisms between them explicit, adjacent, and checkable.

## Current Codebase Status

For the latest verified build/audit snapshot, use
[CODEBASE_STATUS.md](CODEBASE_STATUS.md).

## What Is Being Formalized

The stable grammar is the semantic representation ladder defined in
[lean/InfoGeometry/Meta/Architecture.lean](../lean/InfoGeometry/Meta/Architecture.lean)
and enforced by
[lean/InfoGeometry/Audit.lean](../lean/InfoGeometry/Audit.lean).

The active representation depths are:

| `RepDepth` | Meaning |
|---|---|
| `count` | raw counts, positive representatives, mass data |
| `projective` | gauge, positive rays, relative potentials |
| `operator` | diagonal operator lifts, inverse-kernel algebra |
| `krein` | split quadratic, Clifford, doubled and phase-space geometry |
| `transport` | Bogoliubov, Weyl, and related transport layers |
| `thermo` | Gibbs, Sinkhorn, attention, and thermal packaging |

The design rule is:

- owner files define the lowest natural surface
- translator files move one adjacent step
- coherence files prove adjacent composites agree
- capstones summarize lower content without pretending to be roots

The maintained tooling layer now has two operator surfaces:

- DAG refresh and reporting under [lean/DAG](../lean/DAG) and [tools/infra](../tools/infra)
- server-backed semantic and proof-state inspection under [tools/frontier](../tools/frontier)

The first is authoritative memory for whole-repo structure. The second is the
interactive elaboration surface closest to the Lean editor infoview.

## Current Live Trunks

### Count -> projective -> operator

The most stable lower trunk remains:

- [PositiveMeasure.lean](../lean/InfoGeometry/PositiveMeasure.lean)
- [Normalize.lean](../lean/InfoGeometry/Projective/Normalize.lean)
- [PositiveRayCore.lean](../lean/InfoGeometry/Canonical/PositiveRayCore.lean)
- [RelativePotentialCore.lean](../lean/InfoGeometry/Canonical/RelativePotentialCore.lean)
- [RelativePotentialCountBridge.lean](../lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean)
- [RelativeSurprisalOperatorLift.lean](../lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean)

This corridor is the clean benchmark for nonvacuous adjacent translation.

### Corrected phase-space generalized-metric trunk

The corrected owner lane is now real and no longer speculative:

- [NeutralPhaseSpaceCore.lean](../lean/InfoGeometry/Clifford/NeutralPhaseSpaceCore.lean)
- [NeutralPhaseSpaceDoubledBridge.lean](../lean/InfoGeometry/Clifford/NeutralPhaseSpaceDoubledBridge.lean)
- [PhaseSpaceGeneralizedMetric.lean](../lean/InfoGeometry/Clifford/PhaseSpaceGeneralizedMetric.lean)
- [PhaseSpaceGeneralizedMetricChiralityBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpaceGeneralizedMetricChiralityBridge.lean)

What is already true on this lane:

- the owner carrier is `E × E*`
- the neutral pairing is explicit
- the generalized-metric owner algebra is closed
- the `B`-twisted realized polarization and realized `±` projectors exist on the doubled carrier

### Polarized and recomposition junction

The corrected owner now reaches the maintained polarized/recomposition lane:

- [PhaseSpacePolarizedBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpacePolarizedBridge.lean)
- [PhaseSpaceRecompositionBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpaceRecompositionBridge.lean)
- [RelativeModularSingularization.lean](../lean/InfoGeometry/Canonical/RelativeModularSingularization.lean)

Current status:

- owner-side lifts and transports are real
- realized generalized-metric projector factorization now exists at the junction
- boundary singularization is now explicitly handled via generalized inverses

### KKT, inverse-kernel, and conformal corridor

The corrected owner also now feeds the KKT/conformal side:

- [KKTCore.lean](../lean/InfoGeometry/Canonical/KKTCore.lean)
- [EPDefectAlgebra.lean](../lean/InfoGeometry/Canonical/EPDefectAlgebra.lean)
- [KKTGeneralizedInverseBridge.lean](../lean/InfoGeometry/Canonical/KKTGeneralizedInverseBridge.lean)
- [PhaseSpaceConformalKKTBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpaceConformalKKTBridge.lean)
- [PhaseSpaceCausalFlowBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpaceCausalFlowBridge.lean)

This is now a real causal trunk from phase-space owner data to conformal and recomposition leaves.

### Weyl and Quantum Geometric Tensor branch

The Weyl branch is now welded to the operator spine:

- [ConformalAnomalySource.lean](../lean/InfoGeometry/Canonical/ConformalAnomalySource.lean)
- [EinsteinAnomalyOperator.lean](../lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean)
- [GeometricTensorOperatorLift.lean](../lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean)
- [TransportLieDerivative.lean](../lean/InfoGeometry/Canonical/TransportLieDerivative.lean)

Current status:

- Einstein anomalies are lifted to the doubled carrier
- the Quantum Geometric Tensor (QGT) is derived from operator transport laws
- infinitesimal transport is formalized via Lie derivatives of exponential conjugation

## Current Closure Backlog

For the live closure ledger (fixed points, open fixtures, and priority
elimination order after `9d81730`), see:

- [analytic_closure_backlog.md](analytic_closure_backlog.md)
