# Theory Canopy

This file is a maintained code map, not a claim about final mathematical primitivity.

## Lower substrate families

The current lower layers of the repository are spread across:
- `Core`
- `Convex`
- `Measure`
- `MeasureProjective`
- `Projective`
- `Krein`
- `Singular`
- `Jordan`
- `Quantum` and `KK` bedrock files where appropriate

## Canonical bridge families

The largest canonical bridge families currently include:
- projective/ray/potential spine: `ProjectiveStateCore`, `PositiveRayCore`, `RelativeGeneratorCore`, `RelativePotentialCore`, `RedLine`
- KMS/modular chain: `SinkhornKMSCore`, `KMSSinkhornSeedState`, `KMSSinkhornScalarPotential`, `TomitaTakesaki`, `ConnesCocycle`, `ConnesArakiCore`, `ConnesArakiTomita`
- geometry chain: `RicciMongeAmpere`, `CalabiYauMetricRicci`, `CalabiYauRNMongeAmpere`, `CalabiYauWBridge`
- operator/index chain: `KasparovCycle`, `AnalyticalIndex`, `Rosetta`, `GrandSynthesis`

## Capstones and consumers

The current crown files are consumers, not roots. Examples include:
- `GrandSynthesis`
- `Rosetta`
- `MasterSynthesis`
- topic-specific synthesis modules under `docs/` and `Canonical/`

The current canonicalization effort tries to keep those files thin and to move reusable lower math into owner files below them.

## How to use this canopy

Use it as a topic map only.
For live structural pressure, read the maintained reports after refresh:
- `reports/dag/structural-hotspots.md`
- `reports/dag/semantic-quotient.md`
- `reports/dag/projection-coloring.md`
