# Theory Canopy

This document is a compact semantic map of the repository's highest theory
layers.

It answers one question:

> If I look at the codebase from the top, what are the main crown, trunk, and
> root structures of the theory?

The repository is best understood as a **layered DAG**, not as a strict binary
tree. Dense semantic hubs live below, while stable umbrella modules expose
cleaner publication surfaces above.

## The Short Picture

The canopy is no longer single-spined. The current verified top-level story has
several real trunks:

1. KK / analytical-index / synthesis:
   `InfoGeometry.KK.KasparovCycle.analyticalIndex`
   -> `InfoGeometry.Canonical.AnalyticalIndex.analyticalIndex`
   -> `InfoGeometry.Canonical.GrandSynthesis.*`
2. source-tension / Rosetta / modular anomaly:
   `Singular`, `RicciMongeAmpere`, `BogoliubovFockSuper`, `TomitaTakesaki`
   -> `InfoGeometry.Canonical.Rosetta.*`
   -> `InfoGeometry.Quantum.ModularAnomaly.*`
3. discrete Hurwitz shell / RG stationarity:
   `InfoGeometry.Quantum.Hurwitz`
   -> `InfoGeometry.Quantum.HurwitzRGFlow`
   -> `InfoGeometry.Canonical.RGFlow`
4. finite Pfaffian-sign phase boundary:
   `InfoGeometry.Quantum.KitaevChain.index_change_forces_defect_crossing`

The older KK/index route remains the cleanest classical-style vertical bridge,
but it is no longer the only crown-facing corridor worth showing newcomers.

## The Canopy Layers

| Layer | Role | Main file(s) | Key hubs |
| --- | --- | --- | --- |
| Umbrella / Publication Surface | stable top-level façades | `lean/InfoGeometry/All.lean`, `lean/InfoGeometry.lean`, `lean/InfoGeometry/Library.lean`, `lean/InfoGeometry/Canonical/All.lean` | import/publication surface, not the deepest semantic hubs |
| Crown / Capstone Synthesis | highest synthesis surfaces currently visible | `lean/InfoGeometry/Canonical/GrandSynthesis.lean`, `lean/InfoGeometry/Canonical/Rosetta.lean`, `lean/InfoGeometry/Canonical/GrandSynthesisDoubleCopy.lean` | `information_wheeler_dewitt_equivalence_of_fullCapstone`, `rosetta_source_tension_three_presentations`, `modularCPT_source_rosetta` |
| Trunk / Bridge Layer | large vertical transport between roots and capstones | `lean/InfoGeometry/Canonical/AnalyticalIndex.lean`, `lean/InfoGeometry/Canonical/OperatorAlgebraBridge.lean`, `lean/InfoGeometry/Canonical/DoubleCopyUnification.lean` | `analyticalIndex`, `indexInvariantAlong_of_conjugacy`, `double_copy_geometric_equilibrium_imp` |
| Quantum / Modular Branch | real-Majorana, modular, and finite topological shadow layer | `lean/InfoGeometry/Canonical/BogoliubovFockSuper.lean`, `lean/InfoGeometry/Canonical/TomitaTakesaki.lean`, `lean/InfoGeometry/Quantum/ModularAnomaly.lean`, `lean/InfoGeometry/Quantum/KitaevChain.lean` | `unified_anomaly_bridge`, `thermal_berezinian_index`, `index_change_forces_defect_crossing` |
| Discrete / RG Branch | finite shell symmetry feeding RG fixed-point scaffolds | `lean/InfoGeometry/Quantum/Hurwitz.lean`, `lean/InfoGeometry/Quantum/HurwitzRGFlow.lean`, `lean/InfoGeometry/Canonical/RGFlow.lean` | `HurwitzShellAction.InvariantAtScale`, `betaFunction_eq_zero_of_invariantAtScale`, `existsUnique_fixedPoint_of_contracting` |
| Seed / Root Surfaces | compact roots from which the visible trunks grow | `lean/InfoGeometry/KK/KasparovCycle.lean`, `lean/InfoGeometry/Quantum/RealMajoranaCategory.lean`, `lean/InfoGeometry/Canonical/Singular.lean` | `KasparovCycle.analyticalIndex`, `RealMajoranaCore.K`, projector/source-tension scaffolds |

## What Is “Top” In Practice

There are two different meanings of “top” in this repository.

### 1. Import/publication top

The highest build-safe umbrella is:

- `lean/InfoGeometry/All.lean`

The main stable canonical publication surface is:

- `lean/InfoGeometry/Canonical/All.lean`

These files are important, but they are façades. They tell you what is exposed,
not necessarily where the deepest semantic bottlenecks live.

### 2. Semantic/DAG top

The crown is now distributed across several large consumer-side surfaces:

- `lean/InfoGeometry/Canonical/GrandSynthesis.lean`
- `lean/InfoGeometry/Canonical/Rosetta.lean`
- `lean/InfoGeometry/Quantum/ModularAnomaly.lean`
- `lean/InfoGeometry/Canonical/GrandSynthesisDoubleCopy.lean`

Those are the files where multiple lower branches are named, transported, or
packaged into larger semantic stories.

## Current Branch Families

### KK / index branch

- `lean/InfoGeometry/KK/KasparovCycle.lean`
- `lean/InfoGeometry/Canonical/AnalyticalIndex.lean`

This remains the cleanest currently verified vertical route.

### Operator-algebra branch

- `lean/InfoGeometry/Canonical/OperatorAlgebraBridge.lean`
- `lean/InfoGeometry/Canonical/BogoliubovFockSuper.lean`

This branch is thinner than `AnalyticalIndex`, but it is a real operator-level
transport lane.

### Rosetta / Weyl / modular branch

- `lean/InfoGeometry/Canonical/Rosetta.lean`
- `lean/InfoGeometry/Quantum/ModularAnomaly.lean`
- `lean/InfoGeometry/Canonical/TomitaTakesaki.lean`
- `lean/InfoGeometry/Canonical/WeylTransport.lean`

This is now a genuine transport corridor, not just a naming shell.

### Synthesis branch

- `lean/InfoGeometry/Canonical/GrandSynthesis.lean`
- `lean/InfoGeometry/Canonical/GrandSynthesisDoubleCopy.lean`

This is the capstone-facing crown.

### Discrete / RG / phase branch

- `lean/InfoGeometry/Quantum/Hurwitz.lean`
- `lean/InfoGeometry/Quantum/HurwitzRGFlow.lean`
- `lean/InfoGeometry/Canonical/RGFlow.lean`
- `lean/InfoGeometry/Quantum/KitaevChain.lean`

This branch captures discrete shell symmetry, RG stationarity, and finite
Pfaffian-sign phase boundaries.

## How To Read The Canopy

If you want the shortest meaningful routes through the theory, choose one of
these entry paths.

### Route A: KK / synthesis trunk

1. `lean/InfoGeometry/Canonical/GeneratedFlow.lean`
2. `lean/InfoGeometry/KK/KasparovCycle.lean`
3. `lean/InfoGeometry/Canonical/AnalyticalIndex.lean`
4. `lean/InfoGeometry/Canonical/OperatorAlgebraBridge.lean`
5. `lean/InfoGeometry/Canonical/GrandSynthesis.lean`

### Route B: modular / CPT / Rosetta trunk

1. `lean/InfoGeometry/Quantum/RealMajoranaCategory.lean`
2. `lean/InfoGeometry/Canonical/BogoliubovFockSuper.lean`
3. `lean/InfoGeometry/Canonical/TomitaTakesaki.lean`
4. `lean/InfoGeometry/Quantum/ModularAnomaly.lean`
5. `lean/InfoGeometry/Canonical/Rosetta.lean`

### Route C: discrete shell / RG / phase trunk

1. `lean/InfoGeometry/Quantum/Hurwitz.lean`
2. `lean/InfoGeometry/Quantum/HurwitzRGFlow.lean`
3. `lean/InfoGeometry/Canonical/RGFlow.lean`
4. `lean/InfoGeometry/Quantum/KitaevChain.lean`

## How This Map Is Produced

This file is informed by:

- trusted semantic block exports
- Skynet v2 frontier packets
- the current generated status page at `docs/auto/index.md`
- the current theorem surface in the synchronized capstone modules

It is therefore a **curated semantic map**, not a raw import listing.

## A Second Deep Root Map

This canopy is centered on the currently visible high-level trunks.

There is also a second, deeper root-centered map focused on:

- Radon-Nikodym density
- relative volume change
- Kähler/RN potential
- Weyl gauge transport
- modular RN data

For that route, read [THEORY_CANOPY_RN_GAUGE.md](/home/goutev/LEAN4/info-geometry-lean/THEORY_CANOPY_RN_GAUGE.md).

## Related Entry Points

- `THEORY_CANOPY_RN_GAUGE.md`
- `README.md`
- `NEWCOMER_PATH.md`
- `UNIFICATION_INDEX.md`
- `lean/DAG/README.md`
- `docs/auto/index.md`
- `SELF_OPTIMIZATION_PROTOCOL.md`
