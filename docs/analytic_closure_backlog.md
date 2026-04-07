# Analytic Closure Backlog

This note is a live backlog sketch for the current repository state.

It is not an authority file and it is not a completeness certificate. It exists
to record the shortest remaining theorem paths after the corrected phase-space
owner and generalized-metric algebra were made real.

## What is already closed enough

The following packets are no longer the primary bottleneck:

- corrected phase-space owner:
  - `lean/InfoGeometry/Clifford/NeutralPhaseSpaceCore.lean`
  - `lean/InfoGeometry/Clifford/NeutralPhaseSpaceDoubledBridge.lean`
- owner-side generalized-metric algebra:
  - `lean/InfoGeometry/Clifford/PhaseSpaceGeneralizedMetric.lean`
- owner-to-doubled chirality and realized projector lane:
  - `lean/InfoGeometry/Canonical/PhaseSpaceGeneralizedMetricChiralityBridge.lean`
- recomposition transport corridor:
  - `lean/InfoGeometry/Canonical/PhaseSpacePolarizedBridge.lean`
  - `lean/InfoGeometry/Canonical/PhaseSpaceRecompositionBridge.lean`
- KKT / conformal causal branch:
  - `lean/InfoGeometry/Canonical/PhaseSpaceConformalKKTBridge.lean`
  - `lean/InfoGeometry/Canonical/PhaseSpaceCausalFlowBridge.lean`
- operator anomaly / QGT frontier:
  - `lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean`
  - `lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean`

The remaining work is now branch junction closure, not owner invention.

## Current highest-value backlog

### 1. Internalize the tomita identification at the projector junction

Current status:
- the polarized and recomposition junctions now consume the realized
  generalized-metric projector lane directly;
- the final identification to the maintained tomita generalized-metric
  projector is still carried as an explicit hypothesis in the strongest
  corollaries.

Next step:
- prove that identification internally for the canonical junction data used by
  the maintained polarized/recomposition corridor.

This is the cleanest next theorem gap.

### 2. Strengthen the operator-level obstruction theorem package

Current status:
- `lean/InfoGeometry/Canonical/ConformalAnomalySource.lean` already owns the
  projector commutator / obstruction scalar link;
- `lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean` now formalizes the
  lifted Einstein anomaly on the doubled carrier;
- `lean/InfoGeometry/Canonical/PhaseSpaceWeylCausalBridge.lean` already reaches
  the scalar obstruction norm and Weyl holonomy;
- the source-driven operator package is now explicit (`SourceSpineAndWeylEndpoint`).

Next step:
- reduce explicit commutation/identification hypotheses inside the source-driven
  package and keep the weld trunk-internal. (Partially addressed by recent
  dilation-source derivation from projector agreement).

This is now a compression task, not a missing-shape task.

### 3. Attach the count/projective trunk at the polarized carrier

Current status:
- the count/projective trunk is real:
  - `lean/InfoGeometry/Canonical/PositiveRayCore.lean`
  - `lean/InfoGeometry/Canonical/RelativePotentialCore.lean`
  - `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean`
  - `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean`
  - `lean/InfoGeometry/Canonical/RelativeModularPolarizedBridge.lean`
- the corrected phase-space trunk is also real.

Next step:
- prove one explicit meeting theorem on the common polarized carrier, instead of
  leaving the trunks merely adjacent.

### 4. Add a twisted end-to-end example

Current status:
- there are concrete example/regression files for recomposition and
  generalized-metric surfaces;
- there is not yet one example that runs through the full current trunk with a
  nonzero `B` twist.

Next step:
- add one finite-dimensional model that computes:
  - owner generalized metric,
  - realized doubled projectors,
  - polarized fixation,
  - recomposition transport/coherence,
  - conformal or Weyl output where feasible.

### 5. Strengthen the Tomita / Bogoliubov branch

Current status:
- `lean/InfoGeometry/Canonical/TomitaTakesaki.lean`
- `lean/InfoGeometry/Canonical/BogoliubovTransport.lean`
- `lean/InfoGeometry/Canonical/TransportLieDerivative.lean`
- `lean/InfoGeometry/Canonical/ConnesArakiTomita.lean`

already form a real modular corridor.

Next step:
- connect the current corrected owner trunk to this modular branch by explicit
  adjacent bridge theorems, not by high-level prose.

This is closer than KK/index work.
