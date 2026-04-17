# One Theory, Many Presentations

This repository should be read as one theory with several simultaneous
presentations. The mathematical burden is on the adjacent morphisms.

## Foundational Axiom: Goutev’s Principle

The repository is built on **Goutev’s Principle of Absolute Relativity of 
Measurement**:

> No measurement has standalone physical meaning. Every measurement is 
> intrinsically relational. Physical content is invariant under common 
> rescaling of compared magnitudes. 

**Measurement is projective; observables are relational invariants.**
See [Goutevs_Principle.md](Goutevs_Principle.md) for the formal manifesto.

## Representation Grammar

The active grammar is the semantic `RepDepth` taxonomy in
[Architecture.lean](../lean/InfoGeometry/Meta/Architecture.lean),
checked by [Audit.lean](../lean/InfoGeometry/Audit.lean).

| Depth | Meaning |
|---|---|
| `count` | counts, positive representatives, raw mass data |
| `projective` | positive rays, gauge sections, relative potentials |
| `operator` | operator lifts, projector and inverse-kernel algebra |
| `krein` | split quadratic, doubled, Clifford, phase-space geometry |
| `transport` | Bogoliubov, Weyl, and causal transport |
| `thermo` | Gibbs, Sinkhorn, attention, thermal packaging |

The structural rule is simple:

- non-capstone declarations should move only one depth step at a time
- capstones may span further, but they are consumers, not roots

Current gate note:

- `InfoGeometry.LLM` currently compiles under locked build.
- `strictCheck` is currently red due warning-as-error debt.
- standalone [`ProjectorEquivariance.lean`](../lean/InfoGeometry/Canonical/ProjectorEquivariance.lean)
  currently compiles.

For execution order and closure milestones, use
[CleanupImprovementProgram.md](CleanupImprovementProgram.md).

## Current Semantic Roots

The most important current roots are:

Count/projective roots:

- [PositiveMeasure.lean](../lean/InfoGeometry/PositiveMeasure.lean)
- [Normalize.lean](../lean/InfoGeometry/Projective/Normalize.lean)
- [PositiveRayCore.lean](../lean/InfoGeometry/Canonical/PositiveRayCore.lean)
- [RelativePotentialCore.lean](../lean/InfoGeometry/Canonical/RelativePotentialCore.lean)

Corrected phase-space roots:

- [NeutralPhaseSpaceCore.lean](../lean/InfoGeometry/Clifford/NeutralPhaseSpaceCore.lean)
- [NeutralPhaseSpaceDoubledBridge.lean](../lean/InfoGeometry/Clifford/NeutralPhaseSpaceDoubledBridge.lean)
- [PhaseSpaceGeneralizedMetric.lean](../lean/InfoGeometry/Clifford/PhaseSpaceGeneralizedMetric.lean)

Operator/KKT/Quantum roots:

- [KKTCore.lean](../lean/InfoGeometry/Canonical/KKTCore.lean)
- [EinsteinAnomalyOperator.lean](../lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean)
- [GeometricTensorOperatorLift.lean](../lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean)
- [BulkBoundary.lean](../lean/InfoGeometry/Quantum/BulkBoundary.lean)

Tomita/Bogoliubov/Transport roots:

- [TomitaTakesaki.lean](../lean/InfoGeometry/Canonical/TomitaTakesaki.lean)
- [BogoliubovTransport.lean](../lean/InfoGeometry/Canonical/BogoliubovTransport.lean)
- [TransportLieDerivative.lean](../lean/InfoGeometry/Canonical/TransportLieDerivative.lean)

## Current Strongest Trunks

### 1. Count -> projective -> operator

This remains the cleanest lower-to-upper corridor:

- [PositiveMeasure.lean](../lean/InfoGeometry/PositiveMeasure.lean)
- [Normalize.lean](../lean/InfoGeometry/Projective/Normalize.lean)
- [PositiveRayCore.lean](../lean/InfoGeometry/Canonical/PositiveRayCore.lean)
- [RelativePotentialCore.lean](../lean/InfoGeometry/Canonical/RelativePotentialCore.lean)
- [RelativePotentialCountBridge.lean](../lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean)
- [RelativeSurprisalOperatorLift.lean](../lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean)

### 2. Corrected phase-space generalized metric

This trunk is now real, not aspirational:

- [NeutralPhaseSpaceCore.lean](../lean/InfoGeometry/Clifford/NeutralPhaseSpaceCore.lean)
- [NeutralPhaseSpaceDoubledBridge.lean](../lean/InfoGeometry/Clifford/NeutralPhaseSpaceDoubledBridge.lean)
- [PhaseSpaceGeneralizedMetric.lean](../lean/InfoGeometry/Clifford/PhaseSpaceGeneralizedMetric.lean)
- [PhaseSpaceGeneralizedMetricChiralityBridge.lean](../lean/InfoGeometry/Canonical/PhaseSpaceGeneralizedMetricChiralityBridge.lean)

### 3. Transport and Quantum Geometric Tensor

This is the current active frontier trunk:

- [GeometricTensorOperatorLift.lean](../lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean)
- [EinsteinAnomalyOperator.lean](../lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean)
- [TransportLieDerivative.lean](../lean/InfoGeometry/Canonical/TransportLieDerivative.lean)
- [WeylTransport.lean](../lean/InfoGeometry/Canonical/WeylTransport.lean)

What is already closed here:
- the metric readout of operator transport commutators
- the lift of the Einstein anomaly to the doubled carrier
- the infinitesimal Lie derivative law for exponential conjugation

### 4. Spectroscopic/KMS and path-ensemble translator trunk

This branch is the current measurement-relativity and path-weight packaging lane:

- [UnruhKMS.lean](../lean/InfoGeometry/Dynamics/UnruhKMS.lean)
- [SpectroscopicGaugeKMSBridge.lean](../lean/InfoGeometry/Canonical/SpectroscopicGaugeKMSBridge.lean)
- [SpectroscopicGauge.lean](../lean/InfoGeometry/Canonical/SpectroscopicGauge.lean)
- [HestenesGibbsPathIntegral.lean](../lean/InfoGeometry/Canonical/HestenesGibbsPathIntegral.lean)
- [DiscreteRouterHestenesPathBridge.lean](../lean/InfoGeometry/LLM/DiscreteRouterHestenesPathBridge.lean)

What is already closed here:
- KMS compatibility is downstream to owned Unruh flow (not rerooted).
- gauge obstruction and packet-shift surfaces are explicit.
- path-surprisal Gibbs weight is explicit on the doubled carrier.
- LLM Bayes update is bridged to path-Gibbs form under explicit matching assumptions.
