# Gravity / Gauge Topic Map

This is a current owner map, not a live proof summary.

## Current owner modules

Geometry, gauge, and anomaly-source material is currently distributed across:
- `lean/InfoGeometry/Canonical/BogoliubovFockSuper.lean`
- `lean/InfoGeometry/Canonical/ChiralEinsteinBridge.lean`
- `lean/InfoGeometry/Canonical/RicciMongeAmpere.lean`
- `lean/InfoGeometry/Canonical/CalabiYauMetricRicci.lean`
- `lean/InfoGeometry/Canonical/CalabiYauRNMongeAmpere.lean`
- `lean/InfoGeometry/Canonical/CalabiYauWBridge.lean`
- `lean/InfoGeometry/Canonical/WeylGaugeField.lean`
- `lean/InfoGeometry/Canonical/WeylPathHysteresis.lean`
- `lean/InfoGeometry/Canonical/WeylAnomalySource.lean`

## Structural reading

The old monolithic `WeylInformationGauge` and `CalabiYauBridge` stories have been split by ownership. Read the current packet as:
- lower metric and Monge-Ampere geometry;
- Weyl/path-dependence transport;
- anomaly-source forcing;
- higher consumers that re-export or use those lower layers.

## Verification rule

For actual theorems, inspect the owner files. Do not infer live theorem names or current file boundaries from older synthesis prose.
