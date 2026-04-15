# Representation Depth Graph

This report renders the stable representation-depth spine as a bicategorical dictionary of presentations.

## Status
- source audit status: **PASS**
- merged indexed files: `23`
- tracked direct edges: `46`
- Lean-tagged files: `16`
- Lean-tagged declarations: `18`
- role counts: `{'coherence': 4, 'mixed': 1, 'owner': 9, 'translator': 9}`

## Sources
- manual role index: `reports/dag/representation-depth-index.json`
- Lean depth export: `artifacts/dag/representation-depth-tags.json`
- provenance counts: `{'lean': 3, 'lean+manual': 13, 'manual': 7}`

## Interpretation
- objects: representation layers `L0 … Ln`
- primitive 1-morphisms: adjacent translator files with `source_depth = d`, `target_depth = d+1`
- 2-morphisms: coherence files that prove different adjacent composites agree
- capstones: composite consumers that may touch many layers but should define no new skip-level ontology

## Layer Objects
### L0 Count
Raw relative counts, relative volume data, positive-measure representatives.

### L1 ProjectiveGauge
Positive rays, gauge sections, relative log-potentials, normalization/projectivization layer.
Owners:
- `lean/InfoGeometry/Canonical/PositiveRayCore.lean`
- `lean/InfoGeometry/Canonical/RelativePotentialCore.lean`

### L2 Operator
Diagonal operator lift, partition/log-partition calculus, scalar modular Hamiltonian as operator syntax.
Owners:
- `lean/InfoGeometry/Canonical/InformationPartitionCore.lean`
- `lean/InfoGeometry/Convex/HessianGeometry.lean`

### L3 KreinClifford
Split/Krein quadratic geometry, polarized sheets, Dirac/metric compatibility on the doubled carrier.
Owners:
- `lean/InfoGeometry/Canonical/DiracMetricCompatibility.lean`
- `lean/InfoGeometry/Krein/PolarizedSector.lean`
- `lean/InfoGeometry/Krein/SplitQuadratic.lean`
- `lean/InfoGeometry/Krein/SplitQuadraticSheets.lean`
Coherence files touching this layer:
- `lean/InfoGeometry/Canonical/DiagonalMetricModularBridge.lean`
Capstones / composites ending here:
- `lean/InfoGeometry/Canonical/SpectralInference.lean`

### L4 Transport
Bogoliubov transport, Hestenes-frame changes, transported spectral/thermal generators.
Coherence files touching this layer:
- `lean/InfoGeometry/Canonical/KreinDiracWeightFunctionalLift.lean`

### L5 ThermoAttention
Gibbs states, Sinkhorn balance, softmax/attention phenomenology.
Owners:
- `lean/InfoGeometry/Convex/LogSumExp.lean`
Coherence files touching this layer:
- `lean/InfoGeometry/Canonical/AttentionPolarizedGibbsBridge.lean`
- `lean/InfoGeometry/Canonical/AttentionPolarizedSinkhornBridge.lean`
Capstones / composites ending here:
- `lean/InfoGeometry/Canonical/AttentionPolarizedSplit.lean`

## Primitive Translator Steps
### L0 → L1
- `lean/InfoGeometry/Canonical/RelativePotentialCountBridge.lean`

### L1 → L2
- `lean/InfoGeometry/Canonical/RelativeSurprisalOperatorLift.lean`

### L2 → L3
- missing

### L3 → L4
- `lean/InfoGeometry/Canonical/BogoliubovPolarizationBridge.lean`
- `lean/InfoGeometry/Canonical/KreinDiracSpectralLift.lean`
- `lean/InfoGeometry/Canonical/SplitCliffordThermalBridge.lean`

### L4 → L5
- `lean/InfoGeometry/Canonical/AttentionPolarizedSplit.lean`

## Forbidden Skips
- `L0→L2`, `L0→L3`, `L0→L4`, `L0→L5`, `L1→L3`, `L1→L4`, `L1→L5`, `L2→L4`, `L2→L5`, `L3→L5`

## Observed Dependency Bands
| Consumer interval | Dependency interval | Status | File edges | Decl edges |
| --- | --- | --- | ---: | ---: |
| `0→1` | `1→1` | `healthy` | 4 | 97 |
| `1→1` | `1→1` | `healthy` | 4 | 96 |
| `3→4` | `3→4` | `healthy` | 4 | 14 |
| `3→3` | `3→3` | `healthy` | 3 | 57 |
| `3→4` | `2→3` | `healthy` | 3 | 50 |
| `3→4` | `2→4` | `healthy` | 3 | 20 |
| `3→4` | `2→2` | `healthy` | 3 | 18 |
| `1→2` | `1→1` | `healthy` | 2 | 73 |
| `2→3` | `2→2` | `healthy` | 2 | 71 |
| `2→3` | `3→3` | `healthy` | 2 | 31 |
| `5→5` | `4→5` | `healthy` | 2 | 21 |
| `4→5` | `3→3` | `healthy` | 2 | 10 |
| `5→5` | `5→5` | `healthy` | 2 | 8 |
| `1→2` | `0→1` | `healthy` | 1 | 144 |
| `2→3` | `0→1` | `healthy` | 1 | 97 |
| `3→3` | `2→2` | `healthy` | 1 | 39 |
| `2→4` | `2→3` | `healthy` | 1 | 25 |
| `2→3` | `2→3` | `healthy` | 1 | 22 |
| `4→5` | `5→5` | `healthy` | 1 | 13 |
| `2→3` | `1→2` | `healthy` | 1 | 8 |
| `1→2` | `2→2` | `healthy` | 1 | 5 |
| `2→4` | `3→4` | `healthy` | 1 | 4 |
| `2→4` | `2→2` | `healthy` | 1 | 2 |

## Review Surface
- `lean/InfoGeometry/Canonical/ChiralTorsionRelativeVolume.lean`: Still imports quarantined BeliefDynamics; likely a facade or missing primitive translator.
- `lean/InfoGeometry/Canonical/ConformalAlgebra.lean`: Depends on structural primitives currently owned by quarantined ChiralCliffordBridge.
- `lean/InfoGeometry/Canonical/CountEmergentFlow.lean`: Still imports quarantined HolographicEmergence; likely a higher-level facade rather than an adjacent-depth translator.
