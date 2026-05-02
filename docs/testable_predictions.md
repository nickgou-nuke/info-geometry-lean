# Measurement-Facing Topics

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

This file is not a catalog of proved physical predictions.

It is a reading guide to theorem families that are closest to measurement-facing
or experimentally suggestive interpretation in the current codebase.

## Nearest live corridors

### 1. Relative-potential and count-facing scalars

- `lean/InfoGeometry/Canonical/RelativePotentialCore.lean`
- `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean`
- `lean/InfoGeometry/Canonical/RelativeModularProjectiveBridge.lean`

This is the nearest corridor for count ratios, modular profiles, and scalar
projective observables.

### 2. Grand-canonical and thermodynamic response

- `lean/InfoGeometry/Core/GrandCanonical.lean`
- `lean/InfoGeometry/GrandCanonical/ResponseMatrix.lean`

This is the nearest corridor for thermodynamic susceptibilities, Hessians, and
multi-parameter response readouts.

### 3. Generalized-metric / chirality / recomposition observables

- `lean/InfoGeometry/Clifford/PhaseSpaceGeneralizedMetric.lean`
- `lean/InfoGeometry/Canonical/PhaseSpaceGeneralizedMetricChiralityBridge.lean`
- `lean/InfoGeometry/Canonical/PhaseSpacePolarizedBridge.lean`
- `lean/InfoGeometry/Canonical/PhaseSpaceRecompositionBridge.lean`

This is the nearest corridor for transport defects, sheet exchange, and
recomposition quantities.

### 4. Conformal / anomaly / Weyl / QGT scalars

- `lean/InfoGeometry/Canonical/PhaseSpaceConformalKKTBridge.lean`
- `lean/InfoGeometry/Canonical/ConformalAnomalySource.lean`
- `lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean`
- `lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean`
- `lean/InfoGeometry/Canonical/PhaseSpaceWeylCausalBridge.lean`
- `lean/InfoGeometry/Canonical/WeylTransport.lean`

This is the nearest corridor for anomaly-like, Weyl-holonomy-like, and Quantum
Geometric Tensor metric readouts.

### 5. Modular / Bogoliubov endpoints

- `lean/InfoGeometry/Canonical/TomitaTakesaki.lean`
- `lean/InfoGeometry/Canonical/BogoliubovTransport.lean`
- `lean/InfoGeometry/Canonical/TransportLieDerivative.lean`
- `lean/InfoGeometry/Canonical/ConnesArakiTomita.lean`

This is the nearest corridor for modular-time or thermal-time interpretation.

## Current caution

None of the above should be read as a finished empirical theory.

The repository currently supports:

- exact operator and scalar bridges in several corridors;
- concrete finite-dimensional examples in selected places; and
- a growing transport architecture.

It does not yet support a closed observational dictionary across all crowns.

## Use rule

Any experimental or physical claim should be reconstructed from current theorem
statements in the cited files. This markdown note is only a guide to where the
nearest measurement-facing packets live.
