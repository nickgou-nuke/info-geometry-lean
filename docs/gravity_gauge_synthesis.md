# Gravity / Gauge Topic Map

This note is a topic map, not a proof summary.

Its purpose is to state where the current gauge-like and geometry-like material
actually lives after the corrected phase-space trunk became the active semantic
center.

## Current live gauge-side corridor

The nearest live gauge/anomaly corridor is now:

- `lean/InfoGeometry/Clifford/PhaseSpaceGeneralizedMetric.lean`
- `lean/InfoGeometry/Canonical/PhaseSpaceGeneralizedMetricChiralityBridge.lean`
- `lean/InfoGeometry/Canonical/PhaseSpaceConformalKKTBridge.lean`
- `lean/InfoGeometry/Canonical/ConformalAnomalySource.lean`
- `lean/InfoGeometry/Canonical/EinsteinAnomalyOperator.lean`
- `lean/InfoGeometry/Quantum/GeometricTensorOperatorLift.lean`
- `lean/InfoGeometry/Canonical/WeylGaugeField.lean`
- `lean/InfoGeometry/Canonical/WeylTransport.lean`
- `lean/InfoGeometry/Canonical/WeylTransportChiralBridge.lean`
- `lean/InfoGeometry/Canonical/PhaseSpaceWeylCausalBridge.lean`

This is the branch where generalized metric, chirality, KKT grading, conformal
obstruction, and Weyl transport currently meet.

## Current geometry-side reading

The repository still contains broader geometry trunks, but they are not the
current semantic center of the closure work. They should be read as adjacent
families, not as the active source of the gauge/anomaly corridor.

So the current reading is:

- corrected phase-space generalized metric is the live geometric owner for the
  chirality/conformal/Weyl corridor;
- Weyl and anomaly are the nearest gauge-like leaves of that trunk;
- broader Ricci / Monge-Ampere / Calabi-Yau geometry remains a separate
  extension family unless an explicit bridge proves otherwise.

## Current open gap

The remaining honest gap is still operator-level:

- the Weyl branch is attached to conformal obstruction,
- but the repo still needs the full operator theorem deriving that obstruction
  from trunk-compatible grading data.

Until that theorem exists, gravity/gauge synthesis remains partial.

## Use rule

Use this file only as a reading guide. For actual theorems, inspect the owner
and bridge files directly.
