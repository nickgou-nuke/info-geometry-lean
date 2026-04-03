# Theory Canopy

This file is a maintained code map, not a claim about final mathematical primitivity.

## Representation Depth Taxonomy

The spine is organized by the native `RepDepth` semantic taxonomy
(defined in `lean/InfoGeometry/Meta/Architecture.lean`):

| Depth | Presentation |
|-------|-------------|
| `count` | Raw relative counts and measure theory |
| `projective` | Ray geometry and normalization sections |
| `operator` | Diagonal operator lifts and commutant calculus |
| `krein` | Split quadratic geometry and Clifford atoms |
| `transport` | Bogoliubov flows and spectral transport |
| `thermo` | Gibbs states and attention surfaces |

Declarations carry `@[rep_depth <level>]` attributes.
Adjacency is enforced by `#audit_architecture` in `Audit.lean`:
non-capstone declarations at depth `d` may only depend on depth `d` or `d − 1`.

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
For live structural pressure, run the Lean-native audit first, then read the maintained reports:
- `lean/InfoGeometry/Audit.lean` — the compiler-enforced adjacency check
- `reports/dag/representation-depth-audit.md`
- `reports/dag/representation-depth-graph.md`
- `reports/dag/theorem-significance.md` — vacuity enforcement report
- `reports/dag/structural-hotspots.md`
- `reports/dag/semantic-quotient.md`
