# Unification Map

This note is a short structural map of the current live unification work.

It is not a proof source. Use Lean files first. Use this file to remember which
trunks are real, where they meet, and which closures are still missing.

## Semantic roots

The current semantic roots are:

- `lean/InfoGeometry/Canonical/PositiveRayCore.lean`
- `lean/InfoGeometry/Canonical/RelativePotentialCore.lean`
- `lean/InfoGeometry/Clifford/NeutralPhaseSpaceCore.lean`
- `lean/InfoGeometry/Clifford/NeutralPhaseSpaceDoubledBridge.lean`
- `lean/InfoGeometry/Clifford/PhaseSpaceGeneralizedMetric.lean`
- `lean/InfoGeometry/Canonical/KKTCore.lean`
- `lean/InfoGeometry/Canonical/EPDefectAlgebra.lean`
- `lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean`
- `lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean`
- `lean/InfoGeometry/Quantum/BulkBoundary.lean`
- `lean/InfoGeometry/Canonical/TomitaTakesaki.lean`

These files own the live algebraic and operator packets. They should be read as
roots or root-near bridges, not as decorative wrappers.

## Current live trunks

### 1. Count / projective / operator trunk

- `lean/InfoGeometry/Canonical/PositiveRayCore.lean`
- `lean/InfoGeometry/Canonical/RelativePotentialCore.lean`
- `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean`
- `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean`
- `lean/InfoGeometry/Canonical/RelativeModularPolarizedBridge.lean`
- `lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean`

This trunk is real. Its open problem is not existence, but junction closure:
it still needs a tighter meeting with the corrected phase-space lane at the
polarized carrier.

### 2. Corrected phase-space / generalized-metric trunk

- `lean/InfoGeometry/Clifford/NeutralPhaseSpaceCore.lean`
- `lean/InfoGeometry/Clifford/NeutralPhaseSpaceDoubledBridge.lean`
- `lean/InfoGeometry/Clifford/PhaseSpaceGeneralizedMetric.lean`
- `lean/InfoGeometry/Canonical/PhaseSpaceGeneralizedMetricChiralityBridge.lean`
- `lean/InfoGeometry/Canonical/PhaseSpaceConformalKKTBridge.lean`

This is now the main geometric carrier for the chirality/conformal leaves.

### 3. Transport and Quantum Geometric Tensor trunk

- `lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean`
- `lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean`
- `lean/InfoGeometry/Canonical/TransportLieDerivative.lean`
- `lean/InfoGeometry/Canonical/WeylTransport.lean`
- `lean/InfoGeometry/Canonical/PhaseSpaceWeylCausalBridge.lean`

This trunk connects infinitesimal transport Laws (Lie derivatives) to operator
anomalies and metric readouts.

## Current meeting points

The main current meeting points (where two or more trunks are proven to agree)
are:

- **doubled carrier:** where the corrected phase-space owner meets the realized
  generalized-metric and Einstein-anomaly lifts;
- **conformal / anomaly junction:** where KKT grading data meets the dilation
  source and projector-obstruction operator;
- **polarized junction:** where the count/projective trunk is adjacent to the
  corrected phase-space trunk.

## Current open junctions

The next real unification gaps are:

1. **projector identification:** derive the realized generalized-metric
   projector identification to the maintained tomita projector internally;
2. **count/phase-space weld:** prove the meeting theorem on the polarized
   carrier for the count and phase-space trunks;
3. **spinor-modular bridge:** formalize the identification between the Majorana
   Kitaev spinor modes and the modular singularization layer.

Until these are closed, unification remains a collection of adjacent trunks
rather than one single manifold.
